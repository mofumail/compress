# Spec-level PNG reference decoder and writer, for testing the Bend decoder.
import zlib, struct

CH = {0: 1, 2: 3, 3: 1, 4: 2, 6: 4}

def chunks(data):
    o = 8
    while o + 12 <= len(data):
        n, = struct.unpack('>I', data[o:o+4]); t = data[o+4:o+8]
        yield t, data[o+8:o+8+n]; o += 12 + n
        if t == b'IEND': break

def paeth(a, b, c):
    p = a + b - c; pa, pb, pc = abs(p-a), abs(p-b), abs(p-c)
    return a if pa <= pb and pa <= pc else (b if pb <= pc else c)

def unfilter(raw, h, rb, bpp):
    out = bytearray(h * rb); q = 0
    for y in range(h):
        t = raw[q]; q += 1
        for x in range(rb):
            a = out[y*rb + x - bpp] if x >= bpp else 0
            b = out[(y-1)*rb + x] if y > 0 else 0
            c = out[(y-1)*rb + x - bpp] if (x >= bpp and y > 0) else 0
            p = [0, a, b, (a+b)//2, paeth(a, b, c)][t]
            out[y*rb + x] = (raw[q] + p) & 255; q += 1
    return out

def decode(data):
    """Canonical pixels: (w, h, ch, bps, bytes)."""
    idat = b''; plte = b''; trns = b''
    for t, d in chunks(data):
        if t == b'IHDR': w, h, dep, ct, _, _, il = struct.unpack('>IIBBBBB', d)
        elif t == b'PLTE': plte = d
        elif t == b'tRNS': trns = d
        elif t == b'IDAT': idat += d
    bpx = CH[ct] * dep; rb = (w * bpx + 7) // 8
    rows = unfilter(zlib.decompress(idat), h, rb, max(1, bpx // 8))
    if ct != 3 and dep >= 8:
        return w, h, CH[ct], dep // 8, bytes(rows)
    samples = []
    for y in range(h):
        for x in range(w):
            bit = x * dep; byte = rows[y*rb + bit//8]
            samples.append((byte >> (8 - dep - bit % 8)) & ((1 << dep) - 1))
    if ct == 0:
        return w, h, 1, 1, bytes(v * (255 // ((1 << dep) - 1)) for v in samples)
    ch = 4 if trns else 3; out = bytearray()
    for v in samples:
        rgb = plte[3*v:3*v+3] if 3*v+3 <= len(plte) else b'\0\0\0'
        out += rgb + (bytes([trns[v] if v < len(trns) else 255]) if ch == 4 else b'')
    return w, h, ch, 1, bytes(out)

def write(path, w, h, ct, dep, rows_bytes, plte=None, trns=None, level=6):
    """A PNG whose rows use filter types 0..4 in turn."""
    bpx = CH[ct] * dep; rb = (w * bpx + 7) // 8; bpp = max(1, bpx // 8)
    raw = bytearray()
    for y in range(h):
        t = y % 5; raw.append(t)
        for x in range(rb):
            v = rows_bytes[y*rb + x]
            a = rows_bytes[y*rb + x - bpp] if x >= bpp else 0
            b = rows_bytes[(y-1)*rb + x] if y > 0 else 0
            c = rows_bytes[(y-1)*rb + x - bpp] if (x >= bpp and y > 0) else 0
            p = [0, a, b, (a+b)//2, paeth(a, b, c)][t]
            raw.append((v - p) & 255)
    def chunk(t, d): return struct.pack('>I', len(d)) + t + d + struct.pack('>I', zlib.crc32(t + d))
    z = zlib.compress(bytes(raw), level)
    idats = [z[i:i+8192] for i in range(0, len(z), 8192)] or [b'']
    out = b'\x89PNG\r\n\x1a\n' + chunk(b'IHDR', struct.pack('>IIBBBBB', w, h, dep, ct, 0, 0, 0))
    if plte: out += chunk(b'PLTE', plte)
    if trns: out += chunk(b'tRNS', trns)
    for d in idats: out += chunk(b'IDAT', d)
    open(path, 'wb').write(out + chunk(b'IEND', b''))

def read_pam(path):
    data = open(path, 'rb').read(); i = data.index(b'ENDHDR\n') + 7
    head = dict(l.split(b' ', 1) for l in data[:i].split(b'\n')[1:-2])
    return int(head[b'WIDTH']), int(head[b'HEIGHT']), int(head[b'DEPTH']), \
        2 if int(head[b'MAXVAL']) > 255 else 1, data[i:]
