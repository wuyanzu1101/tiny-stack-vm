// tinyvm: a stack VM for make.fun's tiny stack ISA v1 (ISA.md). Node 22, no deps.
// Runs every /input/<id>/program.bin on its input.bin; writes stdout.bin + exit.txt.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const enc = new TextEncoder();

// opcode -> [immediate bytes, pops, pushes]
const T = new Map([
  [0x00, [0, 0, 0]], [0x01, [1, 0, 1]], [0x02, [4, 0, 1]], [0x03, [0, 1, 0]],
  [0x04, [0, 1, 2]], [0x05, [0, 2, 2]], [0x06, [0, 2, 3]], [0x07, [0, 3, 3]],
  [0x10, [0, 2, 1]], [0x11, [0, 2, 1]], [0x12, [0, 2, 1]], [0x13, [0, 2, 1]],
  [0x14, [0, 2, 1]], [0x15, [0, 2, 1]], [0x16, [0, 2, 1]], [0x17, [0, 1, 1]],
  [0x18, [0, 2, 1]], [0x19, [0, 2, 1]], [0x1a, [0, 2, 1]], [0x1b, [0, 1, 1]],
  [0x1c, [0, 2, 1]], [0x1d, [0, 2, 1]], [0x1e, [0, 2, 1]], [0x20, [0, 2, 1]],
  [0x21, [0, 2, 1]], [0x22, [0, 2, 1]], [0x30, [2, 0, 0]], [0x31, [2, 1, 0]],
  [0x32, [2, 1, 0]], [0x33, [2, 0, 0]], [0x34, [0, 0, 0]], [0x40, [0, 1, 1]],
  [0x41, [0, 2, 0]], [0x50, [0, 1, 0]], [0x51, [0, 1, 0]], [0x52, [0, 0, 1]],
  [0x53, [0, 1, 0]],
]);

// Run one program; returns [bytes, exit]. A trap ends it at once, keeping prior output.
function run(P, inp) {
  const n = P.length;
  const D = new Int32Array(256); // data stack
  let sp = 0;
  const C = new Int32Array(64); // call stack
  let cp = 0;
  const M = new Int32Array(256); // memory
  const out = new Uint8Array(65536);
  let ol = 0, ip = 0, pc = 0, st = 0;
  const end = (e) => [out.subarray(0, ol), e];
  for (;;) {
    if (st === 1000000) return end(10); // step limit
    if (pc < 0 || pc >= n) return end(9); // pc outside program
    const op = P[pc];
    const t = T.get(op);
    if (!t) return end(5); // unknown opcode
    const im = t[0], po = t[1], pu = t[2];
    if (pc + im >= n) return end(9); // immediate cut off
    st++;
    const nx = pc + 1 + im;
    if (sp < po) return end(2); // stack underflow
    if (sp - po + pu > 256) return end(3); // stack overflow
    pc = nx;
    switch (op) {
      case 0x00: return end(0); // HALT
      case 0x01: D[sp++] = (P[nx - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 0x02: D[sp++] = P[nx - 4] | (P[nx - 3] << 8) | (P[nx - 2] << 16) | (P[nx - 1] << 24); break; // PUSH32
      case 0x03: sp--; break; // POP
      case 0x04: D[sp] = D[sp - 1]; sp++; break; // DUP
      case 0x05: { const v = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = v; break; } // SWAP
      case 0x06: D[sp] = D[sp - 2]; sp++; break; // OVER
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; } // ROT
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break; // NEG (wraps)
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break; // NOT
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1], a = D[sp - 2];
        let r;
        switch (op) {
          case 0x10: r = (a + b) | 0; break; // ADD
          case 0x11: r = (a - b) | 0; break; // SUB
          case 0x12: r = Math.imul(a, b); break; // MUL, low 32 bits
          case 0x13: if (b === 0) return end(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break; // DIV
          case 0x14: if (b === 0) return end(4); r = b === -1 ? 0 : (a % b) | 0; break; // MOD
          case 0x15: if (b === 0) return end(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break; // DIVU
          case 0x16: if (b === 0) return end(4); r = ((a >>> 0) % (b >>> 0)) | 0; break; // MODU
          case 0x18: r = a & b; break; // AND
          case 0x19: r = a | b; break; // OR
          case 0x1a: r = a ^ b; break; // XOR
          case 0x1c: r = a << (b & 31); break; // SHL
          case 0x1d: r = a >> (b & 31); break; // SHR, arithmetic
          case 0x1e: r = (a >>> (b & 31)) | 0; break; // SHRU, logical
          case 0x20: r = a === b ? 1 : 0; break; // EQ
          case 0x21: r = a < b ? 1 : 0; break; // LT, signed
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU, unsigned
        }
        sp -= 2; D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ
        const rel = ((P[nx - 2] | (P[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = D[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33: // CALL
        if (cp === 64) return end(7);
        C[cp++] = nx;
        pc = P[nx - 2] | (P[nx - 1] << 8);
        break;
      case 0x34: // RET
        if (cp === 0) return end(8);
        pc = C[--cp];
        break;
      case 0x40: { // LOAD
        const a = D[sp - 1];
        if (a < 0 || a >= 256) return end(6);
        D[sp - 1] = M[a];
        break;
      }
      case 0x41: { // STORE
        const a = D[sp - 1], v = D[sp - 2];
        if (a < 0 || a >= 256) return end(6);
        sp -= 2; M[a] = v;
        break;
      }
      case 0x50: { // PRINT
        const b = enc.encode(String(D[sp - 1]));
        if (ol + b.length > 65536) return end(11);
        sp--; out.set(b, ol); ol += b.length;
        break;
      }
      case 0x51: // PUTC: one byte, v & 255
        if (ol + 1 > 65536) return end(11);
        out[ol++] = D[--sp] & 255;
        break;
      case 0x52: D[sp++] = ip < inp.length ? inp[ip++] : -1; break; // IN
      default: return end(D[--sp] & 255); // EXIT (0x53), low byte
    }
  }
}

// One unreadable instance must not kill the set: fall back to empty + trap 9.
for (const id of readdirSync(I, { withFileTypes: true }).filter(d => d.isDirectory()).map(d => d.name).sort()) {
  let out = new Uint8Array(0), exit = 9;
  try { [out, exit] = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin'))); } catch {}
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), out);
  writeFileSync(join(O, id, 'exit.txt'), String(exit) + '\n');
}
