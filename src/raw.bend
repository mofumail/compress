import Base

# Raw octet output. See ffi/write_bytes.c for why Base's File.write
# cannot be used for binary data.
def write_bytes(file: File, bytes: List<&2, U32>) ->
  IO(File & Result<&1, &1, U32 & String, Unit>):
  import "./ffi/write_bytes.c"
  import "./ffi/write_bytes.js"

# Array I/O for the fast path (see ffi/read_arrays.c): each chunk is an
# Array<U32>, one byte per slot, with its byte count in the last slot.
def read_arrays(file: File, max: U32, k: U32) ->
  IO(File & Result<&1, &1, U32 & String, List<&1, Array<U32>>>):
  import "./ffi/read_arrays.c"
  import "./ffi/read_arrays.js"

def read_blob_arrays(file: File, max: U32) ->
  IO(File & Result<&1, &1, U32 & String, List<&1, Array<U32>>>):
  import "./ffi/read_blob_arrays.c"
  import "./ffi/read_blob_arrays.js"

def write_arrays(file: File, xs: List<&1, Array<U32>>) ->
  IO(File & Result<&1, &1, U32 & String, Unit>):
  import "./ffi/write_arrays.c"
  import "./ffi/write_arrays.js"

# A `skip`-byte header, then records of `rhdr` header bytes (the first
# four: the payload length, big-endian) and a payload; one block each.
def read_records(file: File, max: U32, skip: U32, rhdr: U32) ->
  IO(File & Result<&1, &1, U32 & String, List<&1, Array<U32>>>):
  import "./ffi/read_records.c"
  import "./ffi/read_records.js"
