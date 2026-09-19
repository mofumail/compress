import { readSync, writeSync } from "fs";

// JS twins of the array effects: an Array<U32> is a plain JS array here.
function readAll(fd, max) {
  const buf = Buffer.alloc(max);
  let got = 0, n = 1;
  while (n > 0 && got < max) { n = readSync(fd, buf, got, max - got, null); got += n; }
  return buf.subarray(0, got);
}

// bytes packed four per slot, little-endian, count in the last slot
function arr(bytes) {
  let size = 2;
  while (size < Math.ceil(bytes.length / 4) + 1) size *= 2;
  const a = new Array(size).fill(0);
  for (let i = 0; i < bytes.length; i++) a[i >> 2] |= bytes[i] << (8 * (i & 3));
  for (let i = 0; i < size; i++) a[i] >>>= 0;
  a[size - 1] = bytes.length;
  return a;
}

function list(xs) {
  let l = { $: "Nil" };
  for (let i = xs.length - 1; i >= 0; i--) l = { $: "Con", head: xs[i], tail: l };
  return l;
}

export function read_arrays(file, max, k) {
  const b = readAll(file, Number(max)), n = b.length, out = [];
  k = Math.max(1, Number(k));
  for (let i = 0; i < k; i++) out.push(arr(b.subarray(Math.floor(i * n / k), Math.floor((i + 1) * n / k))));
  return [file, { $: "Done", value: list(out) }];
}

export function read_blob_arrays(file, max) {
  const b = readAll(file, Number(max)), out = [];
  for (let o = 5; o + 328 <= b.length;) {
    let len = 328 + b.readUInt32BE(o);
    if (o + len > b.length) len = b.length - o;
    out.push(arr(b.subarray(o, o + len)));
    o += len;
  }
  return [file, { $: "Done", value: list(out) }];
}

export function write_arrays(file, xs) {
  const out = [];
  for (let s = xs; s.$ === "Con"; s = s.tail) {
    const a = s.head, len = Math.min(a[a.length - 1], (a.length - 1) * 4);
    for (let i = 0; i < len; i++) out.push((a[i >> 2] >>> (8 * (i & 3))) & 0xFF);
  }
  writeSync(file, Buffer.from(out));
  return [file, { $: "Done", value: { $: "Unit" } }];
}

export function read_records(file, max, skip, rhdr) {
  const b = readAll(file, Number(max)), out = [];
  skip = Number(skip); rhdr = Number(rhdr);
  out.push(arr(b.subarray(0, Math.min(skip, b.length))));
  for (let o = skip; rhdr >= 4 && o + rhdr <= b.length;) {
    let len = rhdr + b.readUInt32BE(o);
    if (o + len > b.length) len = b.length - o;
    out.push(arr(b.subarray(o, o + len)));
    o += len;
  }
  return [file, { $: "Done", value: list(out) }];
}
