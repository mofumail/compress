import { writeSync } from "fs";

export function write_bytes(file, bytes) {
  const out = [];
  for (let s = bytes; s.$ === "Con"; s = s.tail) out.push(Number(s.head) & 0xFF);
  writeSync(file, Buffer.from(out));
  return [file, { $: "Done", value: { $: "Unit" } }];
}
