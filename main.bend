import Base
import ./src/byte.bend as B
import ./src/codec.bend as Codec
import ./src/raw.bend as Raw
import ./src/chunks.bend as Chunks
import ./src/fast.bend as F
import ./src/atree.bend as T
import ./src/png.bend as P
import ./src/image.bend as Img
import ./src/webp.bend as W

# BZ_MODE 0 = compress (parallel)   2 = decompress (parallel)
#         1 = compress (sequential) 3 = decompress (sequential)
#   The modes above run the fast codec (src/fast.bend). Offset by 10 they
#   run the proven reference codec (src/codec.bend) instead, which writes
#   the same format: 10, 11, 12, 13.
#         4 = fast I/O only: read the chunk arrays, write them back
#        20 = PNG/WebP to .bzi (parallel)   22 = .bzi to PAM (parallel)
#        21 = PNG/WebP to .bzi (sequential) 23 = .bzi to PAM (sequential)
#        24 = PNG/WebP to PAM (decode only)
#        14 = identity (I/O only)
#        15 = split into chunks and join back (no compression)
# BZ_IN / BZ_OUT are paths, BZ_SIZE the input's exact length in bytes,
# BZ_DEPTH the split depth (2^depth chunks).

def rd.fin(fr: File & Result<&1, &1, U32 & String, List<&2, U32>>) ->
  IO(List<&2, U32>):
  (f, r) = fr
  IO.bind(Unit, List<&2, U32>, File.close(f),
    u => IO.pass(List<&2, U32>, r))

def rd.go(n: U32, f: File) -> IO(List<&2, U32>):
  IO.bind(File & Result<&1, &1, U32 & String, List<&2, U32>>,
    List<&2, U32>, File.read_bytes(f, n), rd.fin)

def read_file(path: String, n: U32) -> IO(List<&2, U32>):
  IO.bind(File, List<&2, U32>, IO.try(File, File.open(path, "r")), rd.go(n))

def wr.fin(fr: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (f, r) = fr
  IO.bind(Unit, Unit, IO.pass(Unit, r), u => File.close(f))

def wr.go(bs: List<&2, U32>, f: File) -> IO(Unit):
  IO.bind(File & Result<&1, &1, U32 & String, Unit>, Unit,
    Raw.write_bytes(f, bs), wr.fin)

def write_file(path: String, bs: List<&2, U32>) -> IO(Unit):
  IO.bind(File, Unit, IO.try(File, File.open(path, "w")), wr.go(bs))

def num(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def run(mode: Nat, +d: Nat, +w: B.Octets()) -> B.Octets():
  match mode:
    case 0n:
      Codec.compress(d, w)
    case 1n+a:
      match a:
        case 0n:
          Codec.compress_seq(d, w)
        case 1n+b:
          match b:
            case 0n:
              Codec.decompress(w)
            case 1n+c:
              match c:
                case 0n:
                  Codec.decompress_seq(w)
                case 1n+e:
                  match e:
                    case 0n:
                      w
                    case 1n+g:
                      Chunks.join(U32, Chunks.of(U32, d, w))

# ------------------------------------------------ the fast pipeline
# Chunks travel as arrays (see src/ffi/read_arrays.c): read as 2^d arrays,
# paired up into a balanced tree, compressed in parallel over it, and
# written back from the leaves. No step touches the whole file as a list.

def ra.fin(fr: File & Result<&1, &1, U32 & String, T.Arrs()>) -> IO(T.Arrs()):
  (f, r) = fr
  IO.bind(Unit, T.Arrs(), File.close(f), u => IO.pass(T.Arrs(), r))

def load_arrays(path: String, n: U32, +k: U32) -> IO(T.Arrs()):
  IO.bind(File, T.Arrs(), IO.try(File, File.open(path, "r")),
    f => IO.bind(File & Result<&1, &1, U32 & String, T.Arrs()>, T.Arrs(),
      Raw.read_arrays(f, n, k), ra.fin))

def load_blobs(path: String, n: U32) -> IO(T.Arrs()):
  IO.bind(File, T.Arrs(), IO.try(File, File.open(path, "r")),
    f => IO.bind(File & Result<&1, &1, U32 & String, T.Arrs()>, T.Arrs(),
      Raw.read_blob_arrays(f, n), ra.fin))

def save_arrays(path: String, xs: T.Arrs()) -> IO(Unit):
  IO.bind(File, Unit, IO.try(File, File.open(path, "w")),
    f => IO.bind(File & Result<&1, &1, U32 & String, Unit>, Unit,
      Raw.write_arrays(f, xs), wr.fin))

def fast_comp(par: Bool, path: String, dest: String, +n: Nat, +depth: Nat) -> IO(Unit):
  +d = Codec.fit(depth, n)
  IO.bind(T.Arrs(), Unit, load_arrays(path, U32.from_nat(n), U32.pow(2, d)),
    xs => save_arrays(dest, Con{F.of_list([66, 90, 55, 55, U32.from_nat(d)]),
      T.leaves(T.pick_comp(par, T.collapse(40n, T.wrap(xs))), Nil{})}))

def fast_dec(par: Bool, path: String, dest: String, +n: Nat) -> IO(Unit):
  IO.bind(T.Arrs(), Unit, load_blobs(path, U32.from_nat(n)),
    xs => save_arrays(dest, T.leaves(T.pick_dec(par, T.collapse(40n, T.wrap(xs))), Nil{})))

# Mode 4: read the chunk arrays and write them straight back -- the
# serial I/O floor under the fast modes.
def fast_id(path: String, dest: String, +n: Nat, +depth: Nat) -> IO(Unit):
  +d = Codec.fit(depth, n)
  IO.bind(T.Arrs(), Unit, load_arrays(path, U32.from_nat(n), U32.pow(2, d)),
    xs => save_arrays(dest, xs))

def slow(mode: Nat, path: String, dest: String, +n: Nat, +d: Nat) -> IO(Unit):
  IO.bind(List<&2, U32>, Unit, read_file(path, U32.from_nat(n)),
    ws => write_file(dest, run(mode, d, ws)))

def dispatch(mode: Nat, path: String, dest: String, +n: Nat, +d: Nat) -> IO(Unit):
  match mode:
    case 0n:
      fast_comp(True{}, path, dest, n, d)
    case 1n+a:
      match a:
        case 0n:
          fast_comp(False{}, path, dest, n, d)
        case 1n+b:
          match b:
            case 0n:
              fast_dec(True{}, path, dest, n)
            case 1n+c:
              match c:
                case 0n:
                  fast_dec(False{}, path, dest, n)
                case 1n+e:
                  match e:
                    case 0n:
                      fast_id(path, dest, n, d)
                    case 1n+h:
                      slow(Nat.sub(e, 6n), path, dest, n, d)

# ------------------------------------------------ images

def load_records(path: String, n: U32, +skip: U32, +rhdr: U32) -> IO(T.Arrs()):
  IO.bind(File, T.Arrs(), IO.try(File, File.open(path, "r")),
    f => IO.bind(File & Result<&1, &1, U32 & String, T.Arrs()>, T.Arrs(),
      Raw.read_records(f, n, skip, rhdr), ra.fin))

def img.pam(im: P.IM, dest: String) -> IO(Unit):
  match im:
    case P.IM{px, +w, +h, +ch, +bps, ok, pal, pch}:
      save_arrays(dest, [F.of_list(P.pam_header(w, h, ch, bps)), px])

def img.ok(ok: Bool, im: P.IM, dest: String, +pam: Bool, +par: Bool) -> IO(Unit):
  match ok:
    case False{}:
      IO.die(Unit, 2, "unsupported image: not PNG or lossless WebP (interlaced PNG, lossy or animated WebP)")
    case True{}:
      match pam:
        case True{}:
          img.pam(P.to_rgb(im), dest)
        case False{}:
          save_arrays(dest, Img.encode(im, par))

def img.check(im: P.IM, dest: String, +pam: Bool, +par: Bool) -> IO(Unit):
  match im:
    case P.IM{px, w, h, ch, bps, +ok, pal, pch}:
      img.ok(ok, P.IM{px, w, h, ch, bps, ok, pal, pch}, dest, pam, par)

def img.first(xs: T.Arrs(), +n: U32, dest: String, +pam: Bool, +par: Bool) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.die(Unit, 2, "empty input")
    case Con{a, r}:
      img.check(W.decode_any(a, n), dest, pam, par)

def png_in(path: String, dest: String, +n: Nat, +pam: Bool, +par: Bool) -> IO(Unit):
  IO.bind(T.Arrs(), Unit, load_arrays(path, U32.from_nat(n), 1),
    xs => img.first(xs, U32.from_nat(n), dest, pam, par))

def bzi_in(path: String, dest: String, +n: Nat, +par: Bool) -> IO(Unit):
  IO.bind(T.Arrs(), Unit, load_records(path, U32.from_nat(n), Img.HDR(), 8),
    xs => save_arrays(dest, Img.decode(xs, par)))

def img.dispatch(m: Nat, path: String, dest: String, +n: Nat) -> IO(Unit):
  match m:
    case 0n:
      png_in(path, dest, n, False{}, True{})
    case 1n+a:
      match a:
        case 0n:
          png_in(path, dest, n, False{}, False{})
        case 1n+b:
          match b:
            case 0n:
              bzi_in(path, dest, n, True{})
            case 1n+c:
              match c:
                case 0n:
                  bzi_in(path, dest, n, False{})
                case 1n+e:
                  png_in(path, dest, n, True{}, True{})

def top(img: Bool, +mode: Nat, path: String, dest: String, +n: Nat, +d: Nat) -> IO(Unit):
  match img:
    case True{}:
      img.dispatch(Nat.sub(mode, 20n), path, dest, n)
    case False{}:
      dispatch(mode, path, dest, n, d)

def top2(+mode: Nat, path: String, dest: String, +n: Nat, +d: Nat) -> IO(Unit):
  top(Nat.is_le(20n, mode), mode, path, dest, n, d)

def main() -> IO(Unit):
  do IO<Unit>:
    mode : String <- IO.try(String, IO.get_env("BZ_MODE"))
    path : String <- IO.try(String, IO.get_env("BZ_IN"))
    dest : String <- IO.try(String, IO.get_env("BZ_OUT"))
    size : String <- IO.try(String, IO.get_env("BZ_SIZE"))
    deep : String <- IO.try(String, IO.get_env("BZ_DEPTH"))
    top2(num(mode), path, dest, num(size), num(deep))
