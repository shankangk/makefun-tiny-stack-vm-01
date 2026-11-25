// A tiny stack VM for make.fun's ISA v1. Reads every instance under the input
// directory and writes its stdout and exit code under the output directory.
// Semantics follow generator/subject/ISA.md: 32-bit wrapping arithmetic, a
// 256-value data stack, a 64-deep call stack, 256 words of memory, and ten
// traps with their own exit codes.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcode byte -> [immediate bytes, values popped, values pushed].
const SPEC = {
  0x00: [0, 0, 0], 0x01: [1, 0, 1], 0x02: [4, 0, 1], 0x03: [0, 1, 0],
  0x04: [0, 1, 2], 0x05: [0, 2, 2], 0x06: [0, 2, 3], 0x07: [0, 3, 3],
  0x10: [0, 2, 1], 0x11: [0, 2, 1], 0x12: [0, 2, 1], 0x13: [0, 2, 1],
  0x14: [0, 2, 1], 0x15: [0, 2, 1], 0x16: [0, 2, 1], 0x17: [0, 1, 1],
  0x18: [0, 2, 1], 0x19: [0, 2, 1], 0x1a: [0, 2, 1], 0x1b: [0, 1, 1],
  0x1c: [0, 2, 1], 0x1d: [0, 2, 1], 0x1e: [0, 2, 1], 0x20: [0, 2, 1],
  0x21: [0, 2, 1], 0x22: [0, 2, 1], 0x30: [2, 0, 0], 0x31: [2, 1, 0],
  0x32: [2, 1, 0], 0x33: [2, 0, 0], 0x34: [0, 0, 0], 0x40: [0, 1, 1],
  0x41: [0, 2, 0], 0x50: [0, 1, 0], 0x51: [0, 1, 0], 0x52: [0, 0, 1],
  0x53: [0, 1, 0],
};

const enc = new TextEncoder();
const MIN = -2147483648;

// Runs one program on its input bytes. Returns [stdout bytes, exit code].
function run(prog, input) {
  const n = prog.length;
  const S = new Int32Array(256); // data stack
  const C = new Int32Array(64); // call stack
  const M = new Int32Array(256); // memory
  const out = new Uint8Array(65536);
  let sp = 0, cp = 0, pc = 0, ip = 0, steps = 0, len = 0;
  const done = (code) => [out.slice(0, len), code];

  for (;;) {
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = prog[pc];
    const spec = SPEC[op];
    if (spec === undefined) return done(5);
    const imm = spec[0];
    if (pc + imm >= n) return done(9);
    steps++;
    const next = pc + 1 + imm;
    if (sp < spec[1]) return done(2);
    if (sp - spec[1] + spec[2] > 256) return done(3);
    pc = next;

    if (op === 0x00) return done(0);
    if (op === 0x01) { S[sp++] = (prog[next - 1] << 24) >> 24; continue; }
    if (op === 0x02) {
      S[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24);
      continue;
    }
    if (op === 0x03) { sp--; continue; }
    if (op === 0x04) { S[sp] = S[sp - 1]; sp++; continue; }
    if (op === 0x05) { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; continue; }
    if (op === 0x06) { S[sp] = S[sp - 2]; sp++; continue; }
    if (op === 0x07) {
      const a = S[sp - 3];
      S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = a;
      continue;
    }
    if (op === 0x17) { S[sp - 1] = -S[sp - 1] | 0; continue; }
    if (op === 0x1b) { S[sp - 1] = ~S[sp - 1]; continue; }

    if (op >= 0x10 && op <= 0x22) {
      const b = S[sp - 1], a = S[sp - 2];
      let r;
      if (op === 0x10) r = (a + b) | 0;
      else if (op === 0x11) r = (a - b) | 0;
      else if (op === 0x12) r = Math.imul(a, b);
      else if (op === 0x13) {
        if (b === 0) return done(4);
        r = a === MIN && b === -1 ? a : (a / b) | 0;
      } else if (op === 0x14) {
        if (b === 0) return done(4);
        r = b === -1 ? 0 : (a % b) | 0;
      } else if (op === 0x15) {
        if (b === 0) return done(4);
        r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
      } else if (op === 0x16) {
        if (b === 0) return done(4);
        r = ((a >>> 0) % (b >>> 0)) | 0;
      } else if (op === 0x18) r = a & b;
      else if (op === 0x19) r = a | b;
      else if (op === 0x1a) r = a ^ b;
      else if (op === 0x1c) r = a << (b & 31);
      else if (op === 0x1d) r = a >> (b & 31);
      else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
      else if (op === 0x20) r = a === b ? 1 : 0;
      else if (op === 0x21) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      sp -= 2;
      S[sp++] = r;
      continue;
    }

    if (op === 0x30 || op === 0x31 || op === 0x32) {
      const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
      let take = op === 0x30;
      if (!take) {
        const v = S[--sp];
        take = op === 0x31 ? v === 0 : v !== 0;
      }
      if (take) pc = next + rel;
      continue;
    }
    if (op === 0x33) {
      if (cp === 64) return done(7);
      C[cp++] = next;
      pc = prog[next - 2] | (prog[next - 1] << 8);
      continue;
    }
    if (op === 0x34) {
      if (cp === 0) return done(8);
      pc = C[--cp];
      continue;
    }
    if (op === 0x40) {
      const addr = S[sp - 1];
      if (addr < 0 || addr >= 256) return done(6);
      S[sp - 1] = M[addr];
      continue;
    }
    if (op === 0x41) {
      const addr = S[sp - 1], v = S[sp - 2];
      if (addr < 0 || addr >= 256) return done(6);
      sp -= 2;
      M[addr] = v;
      continue;
    }
    if (op === 0x50) {
      const bytes = enc.encode(String(S[sp - 1]));
      if (len + bytes.length > 65536) return done(11);
      sp--;
      out.set(bytes, len);
      len += bytes.length;
      continue;
    }
    if (op === 0x51) {
      if (len + 1 > 65536) return done(11);
      out[len++] = S[--sp] & 255;
      continue;
    }
    if (op === 0x52) { S[sp++] = ip < input.length ? input[ip++] : -1; continue; }
    if (op === 0x53) return done(S[--sp] & 255);
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  // One bad instance must not cost the other 39: a failed read still gets
  // an answer in the stated format (worth 0 for that instance only).
  let stdout = new Uint8Array(0);
  let code = 0;
  try {
    [stdout, code] = run(
      new Uint8Array(readFileSync(join(I, id, 'program.bin'))),
      new Uint8Array(readFileSync(join(I, id, 'input.bin'))),
    );
  } catch {
    stdout = new Uint8Array(0);
    code = 0;
  }
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), stdout);
  writeFileSync(join(O, id, 'exit.txt'), code + '\n');
}
