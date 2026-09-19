#!/usr/bin/env python3
"""Image tests: PNG and lossless WebP decoding, and .bzi round trips.

    python3 test/image_test.py [workdir]

Needs ./bz (bend main.bend -o bz), Python 3, numpy and Pillow.
PNG pixels are checked against test/pngref.py (a spec-level decoder,
itself checked against Pillow); WebP pixels against Pillow (libwebp).
"""
import os, sys, random, subprocess
import numpy as np
from PIL import Image
sys.path.insert(0, os.path.dirname(__file__))
import pngref

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
W = sys.argv[1] if len(sys.argv) > 1 else '/tmp/bz-image-test'
os.makedirs(W, exist_ok=True)
rng = np.random.default_rng(7); random.seed(7)

def bz(mode, src, dst, threads):
    return subprocess.run([f'{ROOT}/bz', '--threads', str(threads)], capture_output=True, text=True,
        env={**os.environ, 'BZ_MODE': str(mode), 'BZ_IN': src, 'BZ_OUT': dst,
             'BZ_SIZE': str(os.path.getsize(src)), 'BZ_DEPTH': '8'})

def smooth(h, w, n, depth_max):
    y, x = np.mgrid[0:h, 0:w]
    base = (x * 3 + y * 5 + (x * y) // 7).astype(np.int64)
    return [((base * (k + 1) + rng.integers(0, 9, base.shape)) % depth_max) for k in range(n)]

def png_cases():
    out = []
    for ct, deps in [(0, [1, 2, 4, 8, 16]), (2, [8, 16]), (3, [1, 2, 4, 8]), (4, [8, 16]), (6, [8, 16])]:
        for dep in deps:
            for w, h in [(1, 1), (7, 5), (33, 17), (257, 64)]:
                ch = pngref.CH[ct]; rb = (w * ch * dep + 7) // 8
                planes = smooth(h, w, 4, 1 << dep if dep < 8 else (256 if dep == 8 else 65536))
                if dep >= 8:
                    px = np.stack(planes[:ch], -1).reshape(h, w * ch)
                    rows = px.astype('>u2').tobytes() if dep == 16 else px.astype('u1').tobytes()
                else:
                    rows = bytearray()
                    for yy in range(h):
                        bits = ''.join(format(int(v), f'0{dep}b') for v in planes[0][yy])
                        rows += int(bits + '0' * (rb * 8 - len(bits)), 2).to_bytes(rb, 'big')
                    rows = bytes(rows)
                plte = trns = None
                if ct == 3:
                    plte = bytes(random.randrange(256) for _ in range(3 * (1 << dep)))
                    trns = bytes(random.randrange(256) for _ in range((1 << dep) // 2)) if w % 2 else None
                p = f'{W}/ct{ct}_d{dep}_{w}x{h}.png'
                pngref.write(p, w, h, ct, dep, rows, plte, trns, level=[0, 1, 6, 9][w % 4]); out.append(p)
    for mode in ['L', 'LA', 'RGB', 'RGBA', 'P', '1']:
        p = f'{W}/pil_{mode}.png'
        Image.fromarray(rng.integers(0, 255, (123, 97, 3), dtype=np.uint8), 'RGB').convert(mode).save(p); out.append(p)
    return out

def webp_cases():
    out = []
    def img(h, w, ch, noise=6):
        y, x = np.mgrid[0:h, 0:w]
        return np.stack([((x * (k + 2) + y * (3 - k) + (x * y) // (9 + k)) + rng.integers(0, noise + 1, (h, w))) % 256
                         for k in range(ch)], -1).astype(np.uint8)
    def save(name, arr, mode, **kw):
        p = f'{W}/{name}.webp'; Image.fromarray(arr, mode).save(p, 'WEBP', lossless=True, **kw); out.append(p)
    for m in range(7):
        save(f'rgb_m{m}', img(97, 131, 3), 'RGB', method=m, quality=100)
        save(f'rgba_m{m}', img(64, 77, 4), 'RGBA', method=m, quality=100, exact=True)
    for ncol in (2, 4, 16, 200):
        pal = rng.integers(0, 256, (ncol, 3)).astype(np.uint8)
        idx = (img(83, 121, 1, 2)[..., 0].astype(int) * ncol // 256) % ncol
        for m in (0, 4, 6):
            save(f'pal{ncol}_m{m}', pal[idx], 'RGB', method=m, quality=100)
    save('photo', img(300, 400, 3, 30), 'RGB', method=6, quality=100)
    save('tiny', img(1, 1, 3), 'RGB', method=4)
    return out

def reference(p):
    if p.endswith('.png'):
        return pngref.decode(open(p, 'rb').read())[4]
    im = Image.open(p)
    return im.convert('RGBA' if im.mode == 'RGBA' else 'RGB').tobytes()

def main():
    cases = png_cases() + webp_cases(); fails = 0
    for p in cases:
        exp = reference(p)
        bz(24, p, p + '.pam', 1)
        ok = [pngref.read_pam(p + '.pam')[4] == exp]
        for enc, dec, th in [(20, 22, 16), (21, 23, 1)]:
            bz(enc, p, p + '.bzi', th); bz(dec, p + '.bzi', p + '.out.pam', th)
            ok.append(pngref.read_pam(p + '.out.pam')[4] == exp)
        if not all(ok):
            fails += 1; print('FAIL', os.path.basename(p), ok)
    lossy = f'{W}/lossy.webp'
    Image.fromarray(rng.integers(0, 255, (32, 32, 3), dtype=np.uint8)).save(lossy, 'WEBP', quality=80)
    rejected = bz(24, lossy, lossy + '.pam', 1).returncode != 0
    print(f'{len(cases) - fails}/{len(cases)} images: decode and .bzi round trips exact at 1 and 16 threads')
    print('lossy WebP rejected:', rejected)
    sys.exit(1 if fails or not rejected else 0)

main()
