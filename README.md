# bz

Parallel LZ77/Huffman compressor in Bend. Divides the input into 256 separate chunks and compresses each chunk on a different core.

## Codecs

bz has two codecs that use the same file format.

| Codec | File | Use |
|---|---|---|
| Reference | `src/codec.bend` | The laws apply to this codec, slow. |
| Fast | `src/fast.bend` | The binary uses this codec, tests compare it to the reference codec. |

## Commands

```
bend PROOF.bend          # Check the proofs. Expects: "All terms check."
bend main.bend -o bz     # Builds the binary.
./bench.sh 64 3          # Compare it against gzip. Size of input in MiBs, number of runs.
```

Compress a file with:

```
BZ_MODE=0 BZ_IN=in BZ_OUT=out.bz BZ_SIZE=$(stat -c%s in) BZ_DEPTH=8 ./bz --threads 16
```

Decompress a file with:

```
BZ_MODE=2 BZ_IN=out.bz BZ_OUT=in2 BZ_SIZE=$(stat -c%s out.bz) BZ_DEPTH=8 ./bz --threads 16
```

| Variable | Value |
|---|---|
| `BZ_MODE` | 0: compress. 1: compress on one core. 2: decompress. 3: decompress on one core. 10–13: same but with the reference codec. 4: read and write only (for I/O tests). |
| `BZ_IN`, `BZ_OUT` | Input and output paths. |
| `BZ_SIZE` | Input size as bytes. |
| `BZ_DEPTH` | The input has 2^depth chunks. 8 is optimal. Chunks not smaller than 64 KiB. |

## Results

My machine: Ryzen 9 5950X, 16 cores.  
Input are text files.  
Each value is the median of 3 bench runs.

64 MiB input:

| | Compress, 1 core | Compress, 16 cores | Ratio | Decompress, 1 core | Decompress, 16 cores |
|---|--:|--:|--:|--:|--:|
| bz | 0.701 s | 0.093 s | 4.73 | 0.252 s | 0.061 s |
| gzip -1 | 0.293 s | 0.069 s | 4.57 | 0.133 s | 0.019 s |
| gzip -6 | 1.005 s | 0.143 s | 5.87 | 0.112 s | 0.018 s |

16 MiB input:

| | Compress, 1 core | Compress, 16 cores | Ratio | Decompress, 1 core | Decompress, 16 cores |
|---|--:|--:|--:|--:|--:|
| bz | 0.207 s | 0.030 s | 4.02 | 0.076 s | 0.024 s |
| gzip -1 | 0.083 s | 0.026 s | 4.15 | 0.038 s | 0.011 s |
| gzip -6 | 0.277 s | 0.042 s | 5.23 | 0.032 s | 0.010 s |

Notes:

- gzip uses one core. For the 16-core values, `bench.sh` divides the input into 16 parts and starts 16 gzip processes.
- For decompression, gzip writes 16 files. bz writes one file. This gives gzip an advantage.

## Performance

- Bend does not move a task to a different core after the task starts. With fewer than 256 chunks, bz doesn'tt use all cores.
- At 16 cores, bz uses 38% more CPU time than at 1 core for the same work.
- One bz core is approximately 2.4 times slower than one gzip core.
- Read and write of 64 MiB takes 0.032 s. `cat` takes 0.027 s.

## Laws

`LAWS.bend` contains laws. `PROOF.bend` contains proofs.

| Law | Statement |
|---|---|
| `byte_roundtrip`, `octets_roundtrip` | Conversion between bytes and 32-bit words does not change the data. |
| `bits_roundtrip` | Bit packing does not change the data. The padding is known. |
| `lens_roundtrip` | The code-length header does not change. The data after it does not change. |
| `huff_walk` | Decoding a code gives its symbol. The remaining bits do not change. This is true for all trees. |
| `chunks_roundtrip` | Division into chunks and joining again does not change the data. |
| `chunks_par`, `chunks_par_dec` | Parallel and sequential processing give the same result (reference codec). |
| `fast_par`, `fast_par_dec` | Parallel and sequential processing give the same result (fast codec). |
| `lz_copy_len` | A back-reference of length `len` writes exactly `len` bytes. |
| `lz_lits` | A stream of literals decodes to the same bytes. |
| `take_drop`, `add_succ` | Helper laws. |

`OPEN.bend` contains 4 claims that are not proved:

| Claim | Statement |
|---|---|
| `lz_roundtrip` | The reference LZ77 parser output decodes to the input. |
| `fast_decoder` | The fast LZ77 decoder gives the same output as the reference decoder. |
| `fast_roundtrip` | The fast codec output decodes to the input. |
| `fast_is_reference_format` | The reference decoder decodes the fast codec output. |

Tests check these claims:

- `test/fast_test.bend`: fast and reference codecs, in all directions.
- `test/decode_test.bend`: fast and reference LZ77 decoders.
- `test/lz_test.bend`: small LZ77 inputs.
- `bench.sh`: compares each decompressed file with the input.

## Files

| Path | Contents |
|---|---|
| `LAWS.bend`, `PROOF.bend`, `OPEN.bend` | Laws, proofs, claims that are not proved. |
| `main.bend` | Command-line program. |
| `src/fast.bend` | Fast codec. |
| `src/atree.bend` | Chunk tree for the fast codec. |
| `src/codec.bend`, `src/lz.bend`, `src/huff.bend` | Reference codec. |
| `src/byte.bend`, `src/bits.bend`, `src/tab.bend`, `src/chunks.bend` | Reference codec helpers. |
| `src/raw.bend`, `src/ffi/` | File read and write, in C. |
| `test/` | Tests. `prof.bend` measures the time of each stage. |
| `bench.sh` | Comparison with gzip. |

## Requirements

- Bend 2.0.5 in `~/.bend/bin`. Add this directory to `PATH`.
- Linux with `/proc`. Without `/proc`, file write is slower.
