# bz

bz is a parallel compressor in Bend. It has two parts:

- A general compressor (LZ77 and Huffman). It divides the input into 256 chunks and compresses each chunk on a different core.
- An image compressor. It reads PNG and lossless WebP images and writes `.bzi` files. It divides the image into strips and processes each strip on a different core.

## Codecs

| Codec | File | Use |
|---|---|---|
| Reference | `src/codec.bend` | The laws apply to this codec. It is slow. |
| Fast | `src/fast.bend` | The general compressor uses this codec. It uses the same file format as the reference codec. Tests compare the two codecs. |
| Image | `src/image.bend` | The image compressor. It filters rows (PNG filters), then uses the fast codec with one Huffman code for all strips. |

## Commands

```
bend PROOF.bend               # Check the proofs. Result: "All terms check."
bend main.bend -o bz          # Build the binary.
./bench.sh 64 3               # Compare the general compressor with gzip. 64 MiB input, 3 runs.
./bench_img.sh a.png b.webp   # Measure the image compressor on the given images.
python3 test/image_test.py    # Test the image decoders and the .bzi round trip.
```

Compress a file:

```
BZ_MODE=0 BZ_IN=in BZ_OUT=out.bz BZ_SIZE=$(stat -c%s in) BZ_DEPTH=8 ./bz --threads 16
```

Compress an image, then decompress it:

```
BZ_MODE=20 BZ_IN=a.png BZ_OUT=a.bzi BZ_SIZE=$(stat -c%s a.png) BZ_DEPTH=8 ./bz --threads 16
BZ_MODE=22 BZ_IN=a.bzi BZ_OUT=a.pam BZ_SIZE=$(stat -c%s a.bzi) BZ_DEPTH=8 ./bz --threads 16
```

| Variable | Value |
|---|---|
| `BZ_MODE` | 0: compress. 2: decompress. 1 and 3: the same on one core. 10–13: the same with the reference codec. 4: read and write only (I/O test). |
| | 20: image (PNG or WebP) to `.bzi`. 22: `.bzi` to PAM. 21 and 23: the same on one core. 24: image to PAM (decode only). |
| `BZ_IN`, `BZ_OUT` | Input and output paths. |
| `BZ_SIZE` | Input size in bytes. |
| `BZ_DEPTH` | The input has 2^depth chunks. Use 8. Chunks are not smaller than 64 KiB. |

## Images

Supported input:

- PNG: all color types, bit depths 1 to 16, palettes with transparency. Interlaced PNG is not supported.
- WebP: lossless (VP8L) only, with all four transforms. Lossy and animated WebP are not supported. bz stops with an error message.

Output is PAM (Netpbm). 16-bit samples are kept. Palette images are stored as indices in `.bzi`, and the decoder gives the palette colors.

`.bzi` uses one Huffman code for all strips. Thus each strip adds only 8 bytes, and bz can use 256 strips to use all cores.

Why JPEG and lossy WebP are not supported: their pixels are already approximations. Lossless storage of these pixels makes a file that is larger than the input.

## Results

Machine: Ryzen 9 5950X, 16 cores. Each value is the median of 3 runs.

General compressor, 64 MiB of text:

| | Compress, 1 core | Compress, 16 cores | Ratio | Decompress, 1 core | Decompress, 16 cores |
|---|--:|--:|--:|--:|--:|
| bz | 0.701 s | 0.093 s | 4.73 | 0.252 s | 0.061 s |
| gzip -1 | 0.293 s | 0.069 s | 4.57 | 0.133 s | 0.019 s |
| gzip -6 | 1.005 s | 0.143 s | 5.87 | 0.112 s | 0.018 s |

Image compressor, 8K images (7680 × 4320) and one 1080p image. "From .bzi" is the time to get the pixels from the `.bzi` file:

| Input | Input size | `.bzi` size | Pillow decode | bz decode (1 core) | From `.bzi`, 1 core | From `.bzi`, 16 cores |
|---|--:|--:|--:|--:|--:|--:|
| wall0.png (palette) | 14.2 MB | 16.0 MB (+13%) | 75 ms | 676 ms | 603 ms | 100 ms |
| wall2.png (RGB) | 28.3 MB | 37.7 MB (+34%) | 441 ms | 1108 ms | 1042 ms | 162 ms |
| lockdead.png (RGBA) | 163 KB | 180 KB (+10%) | 9 ms | 60 ms | 68 ms | 18 ms |
| wall0.webp | 12.1 MB | 16.0 MB (+32%) | 309 ms | 4212 ms | 601 ms | 100 ms |
| wall2.webp | 23.6 MB | 37.7 MB (+60%) | 487 ms | 1149 ms | 1042 ms | 162 ms |

Notes:

- gzip uses one core. For the 16-core values, `bench.sh` divides the input into 16 parts and starts 16 gzip processes. For decompression, gzip writes 16 files and bz writes one file. This gives gzip an advantage.
- At 16 cores, the `.bzi` decoder is faster than Pillow on large RGB PNG and on WebP. Pillow is faster on the palette PNG and on small images.
- `.bzi` files are 10–34% larger than PNG and 32–60% larger than lossless WebP.

## Performance limits

- Bend does not move a task to a different core after the task starts. With fewer than 256 chunks or strips, bz does not use all cores.
- PNG and WebP decoding is sequential. One stream codes the full image. The bz decoders are 2.5 to 14 times slower than the C decoders in Pillow. For image to `.bzi` at 16 cores, this decoding takes most of the time.
- At 16 cores, bz uses 38% more CPU time than at 1 core for the same work.
- One bz core is approximately 2.4 times slower than one gzip core.
- The `.bzi` ratio is less than PNG because deflate has a separate Huffman code for distances and changes its codes for each block. bz uses one code for each image.

## Laws

`LAWS.bend` contains the laws. `PROOF.bend` contains the proofs. All 18 laws are proved.

| Law | Statement |
|---|---|
| `byte_roundtrip`, `octets_roundtrip` | Conversion between bytes and 32-bit words does not change the data. |
| `bits_roundtrip` | Bit packing does not change the data. The padding is known. |
| `lens_roundtrip` | The code-length header does not change. The data after it does not change. |
| `huff_walk` | Decoding a code gives its symbol. The remaining bits do not change. This is true for all trees. |
| `chunks_roundtrip` | Division into chunks and joining again does not change the data. |
| `chunks_par`, `chunks_par_dec` | Parallel and sequential processing give the same result (reference codec). |
| `fast_par`, `fast_par_dec` | Parallel and sequential processing give the same result (fast codec). |
| `img_par_a`, `img_par_c`, `img_par_d`, `img_par_dp` | Parallel and sequential processing give the same result (image codec: filter and parse, encode, decode, decode with palette). |
| `lz_copy_len` | A back-reference of length `len` writes exactly `len` bytes. |
| `lz_lits` | A stream of literals decodes to the same bytes. |
| `take_drop`, `add_succ` | Helper laws. |

`OPEN.bend` contains 5 claims that are not proved:

| Claim | Statement |
|---|---|
| `lz_roundtrip` | The reference LZ77 parser output decodes to the input. |
| `fast_decoder` | The fast LZ77 decoder gives the same output as the reference decoder. |
| `fast_roundtrip` | The fast codec output decodes to the input. |
| `fast_is_reference_format` | The reference decoder decodes the fast codec output. |
| `image_roundtrip` | An image encoded to `.bzi` and decoded gives the same pixels. |

Tests check these claims:

- `test/fast_test.bend`: fast and reference codecs, in all directions.
- `test/decode_test.bend`: fast and reference LZ77 decoders.
- `test/lz_test.bend`: small LZ77 inputs.
- `test/image_test.py`: 94 PNG and WebP images. It checks the decoders and the `.bzi` round trip at 1 and 16 threads. PNG pixels are compared with `test/pngref.py` (a decoder from the PNG specification, checked with Pillow). WebP pixels are compared with Pillow.
- `bench.sh` and `bench_img.sh`: compare each output with the input.
- One 16-bit 8K PNG (199 MB of pixels) was compared with the ffmpeg decoder.

## Files

| Path | Contents |
|---|---|
| `LAWS.bend`, `PROOF.bend`, `OPEN.bend` | Laws, proofs, claims that are not proved. |
| `main.bend` | Command-line program. |
| `src/fast.bend` | Fast codec. |
| `src/atree.bend` | Chunk tree for the fast codec. |
| `src/image.bend` | Image codec (`.bzi`). |
| `src/png.bend` | PNG decoder. Row unfilter (also used by the image codec). PAM header. |
| `src/webp.bend` | Lossless WebP decoder. |
| `src/inflate.bend` | Deflate (zlib) decoder, for PNG. |
| `src/codec.bend`, `src/lz.bend`, `src/huff.bend` | Reference codec. |
| `src/byte.bend`, `src/bits.bend`, `src/tab.bend`, `src/chunks.bend` | Reference codec helpers. |
| `src/raw.bend`, `src/ffi/` | File read and write, in C. |
| `test/` | Tests. `prof.bend` measures the time of each stage of the fast codec. |
| `bench.sh`, `bench_img.sh` | Benchmarks. |

## Requirements

- Bend 2.0.5 in `~/.bend/bin`. Add this directory to `PATH`.
- Linux with `/proc`. Without `/proc`, file write is slower.
- For the image tests and `bench_img.sh`: Python 3 with numpy and Pillow.
