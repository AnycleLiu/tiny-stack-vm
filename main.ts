// tiny-vm: an exact interpreter for make.fun's tiny stack ISA v1.
// Built for tiny-stack-vm-01-run-20261122, from the kit's ISA.md (the kit's
// reference VM rules where the prose can be read two ways). One pass per
// program, checks in ISA.md's order — step limit, pc in range, opcode known,
// immediate fits, stack depth — then the instruction. A trap ends the run at
// once, keeps prior output, and reports the trap's code as the exit code.
// Values are 32-bit and wrap; JS bitwise ops and Math.imul give that free.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const SL = 1e6, OL = 65536;
// Opcode metadata by opcode byte: immediate bytes, pops, pushes. Only the
// 38 opcodes ISA.md names are known; any other byte is trap 5.
const K = new Uint8Array(256), IM = new Uint8Array(256), PO = new Uint8Array(256), PU = new Uint8Array(256);
for (const [o, i, a, b] of [[0,0,0,0],[1,1,0,1],[2,4,0,1],[3,0,1,0],[4,0,1,2],[5,0,2,2],[6,0,2,3],[7,0,3,3],[16,0,2,1],[17,0,2,1],[18,0,2,1],[19,0,2,1],[20,0,2,1],[21,0,2,1],[22,0,2,1],[23,0,1,1],[24,0,2,1],[25,0,2,1],[26,0,2,1],[27,0,1,1],[28,0,2,1],[29,0,2,1],[30,0,2,1],[32,0,2,1],[33,0,2,1],[34,0,2,1],[48,2,0,0],[49,2,1,0],[50,2,1,0],[51,2,0,0],[52,0,0,0],[64,0,1,1],[65,0,2,0],[80,0,1,0],[81,0,1,0],[82,0,0,1],[83,0,1,0]]) {
  K[o] = 1; IM[o] = i; PO[o] = a; PU[o] = b;
}
function run(p: Uint8Array, q: Uint8Array) {
  const n = p.length, s = new Int32Array(256);
  let t = 0;
  const c = new Int32Array(64);
  let d = 0;
  const m = new Int32Array(256), o = new Uint8Array(OL);
  let l = 0, g = 0, pc = 0, z = 0;
  const end = (e: number) => ({ out: o.slice(0, l), code: e });
  for (;;) {
    if (z === SL) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = p[pc];
    if (!K[op]) return end(5);
    const im = IM[op];
    if (pc + im >= n) return end(9);
    z++;
    const nx = pc + 1 + im;
    if (t < PO[op]) return end(2);
    if (t - PO[op] + PU[op] > 256) return end(3);
    pc = nx;
    if (op === 0) return end(0); // HALT
    if (op === 1) { s[t++] = (p[nx - 1] << 24) >> 24; continue; } // PUSH8, sign-extended
    if (op === 2) { let v = 0; for (let i = 3; i >= 0; i--) v = (v << 8) | p[nx - 4 + i]; s[t++] = v; continue; } // PUSH32, little-endian
    if (op === 3) { t--; continue; } // POP
    if (op === 4) { s[t] = s[t - 1]; t++; continue; } // DUP
    if (op === 5) { const a = s[t - 1]; s[t - 1] = s[t - 2]; s[t - 2] = a; continue; } // SWAP
    if (op === 6) { s[t] = s[t - 2]; t++; continue; } // OVER
    if (op === 7) { const a = s[t - 3]; s[t - 3] = s[t - 2]; s[t - 2] = s[t - 1]; s[t - 1] = a; continue; } // ROT
    if (op === 23) { s[t - 1] = -s[t - 1] | 0; continue; } // NEG
    if (op === 27) { s[t - 1] = ~s[t - 1]; continue; } // NOT
    if (op >= 16 && op <= 34) { // binary ops: ( a b -- r ), b is the top
      const b = s[t - 1], a = s[t - 2];
      let r = 0;
      if (op === 16) r = (a + b) | 0;
      else if (op === 17) r = (a - b) | 0;
      else if (op === 18) r = Math.imul(a, b);
      else if (op === 19) { if (!b) return end(4); r = a === -2147483648 && b === -1 ? a : Math.trunc(a / b); }
      else if (op === 20) { if (!b) return end(4); r = b === -1 ? 0 : (a % b) | 0; }
      else if (op === 21) { if (!b) return end(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
      else if (op === 22) { if (!b) return end(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
      else if (op === 24) r = a & b;
      else if (op === 25) r = a | b;
      else if (op === 26) r = a ^ b;
      else if (op === 28) r = a << (b & 31);
      else if (op === 29) r = a >> (b & 31);
      else if (op === 30) r = (a >>> (b & 31)) | 0;
      else if (op === 32) r = a === b ? 1 : 0;
      else if (op === 33) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      t -= 2; s[t++] = r; continue;
    }
    if (op >= 48 && op <= 50) { // JMP / JZ / JNZ: signed 16-bit offset from next
      const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
      if (op === 48) pc = nx + rel;
      else { const v = s[--t]; if (op === 49 ? v === 0 : v !== 0) pc = nx + rel; }
      continue;
    }
    if (op === 51) { if (d === 64) return end(7); c[d++] = nx; pc = p[nx - 2] | (p[nx - 1] << 8); continue; } // CALL
    if (op === 52) { if (!d) return end(8); pc = c[--d]; continue; } // RET
    if (op === 64) { const a = s[t - 1]; if (a < 0 || a > 255) return end(6); s[t - 1] = m[a]; continue; } // LOAD
    if (op === 65) { const a = s[t - 1], v = s[t - 2]; if (a < 0 || a > 255) return end(6); t -= 2; m[a] = v; continue; } // STORE ( v addr -- )
    if (op === 80) { const x = String(s[t - 1]); if (l + x.length > OL) return end(11); t--; for (let i = 0; i < x.length; i++) o[l++] = x.charCodeAt(i); continue; } // PRINT
    if (op === 81) { if (l + 1 > OL) return end(11); o[l++] = s[--t] & 255; continue; } // PUTC
    if (op === 82) { s[t++] = g < q.length ? q[g++] : -1; continue; } // IN
    return end(s[--t] & 255); // EXIT
  }
}
// Harness runs `node main.ts` with MAKEFUN_INPUT_DIR / MAKEFUN_OUTPUT_DIR:
// for every <id> under input, write <id>/stdout.bin and <id>/exit.txt.
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  // One bad instance must not take the other 39 with it: a read failure
  // still writes an (empty) answer for that id, and the loop goes on.
  let q = new Uint8Array(0);
  try { q = new Uint8Array(readFileSync(join(I, id, 'input.bin'))); } catch { /* no input file: empty input */ }
  let r = { out: new Uint8Array(0), code: 0 };
  try { r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), q); } catch { /* unreadable program: empty answer */ }
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), r.code + '\n');
}
