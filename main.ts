// tiny-stack-vm: a complete interpreter for make.fun's tiny stack ISA (v1).
// For each instance <id> it runs <id>/program.bin on <id>/input.bin and writes
// <id>/stdout.bin (the bytes written) and <id>/exit.txt (the exit code). Values
// wrap at 32 bits; limits are 256 stack values, 64 return addresses, 256 memory
// words, 1,000,000 steps and 65,536 output bytes. A trap's code is the exit
// code, and output written before a trap is kept.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per-opcode metadata as digit strings indexed by opcode byte, from 0x00 up
// in segments of 16: how many values an opcode pops (POPS) and pushes
// (PUSHES). Digits at unnamed bytes are unused: those bytes trap first.
const POPS =
  '0001122300000000' + '2222222122212220' + '2220000000000000' +
  '0110000000000000' + '1200000000000000' + '1101';
const PUSHES =
  '0110223300000000' + '1111111111111110' + '1110000000000000' +
  '0000000000000000' + '1000000000000000' + '0010';

function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const st = new Int32Array(256);
  const cs = new Int32Array(64);
  const mem = new Int32Array(256);
  const buf = new Uint8Array(65536);
  let sp = 0, csp = 0, olen = 0, inPos = 0, pc = 0, steps = 0;
  const done = (code: number) => ({ out: buf.slice(0, olen), code });

  for (;;) {
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= p.length) return done(9);
    const op = p[pc];
    const known = op <= 0x07 || (op >= 0x10 && op <= 0x1e) || (op >= 0x20 && op <= 0x22) || (op >= 0x30 && op <= 0x34) ||
      op === 0x40 || op === 0x41 || (op >= 0x50 && op <= 0x53);
    if (!known) return done(5);
    const imm = op === 0x01 ? 1 : op === 0x02 ? 4 : op >= 0x30 && op <= 0x33 ? 2 : 0;
    if (pc + imm >= p.length) return done(9);
    steps++;
    const pops = POPS.charCodeAt(op) - 48;
    const pushes = PUSHES.charCodeAt(op) - 48;
    if (sp < pops) return done(2);
    if (sp - pops + pushes > 256) return done(3);
    const next = pc + 1 + imm;
    pc = next;

    // Binary operators: pop b (top), then a, push a result.
    if ((op >= 0x10 && op <= 0x1e && op !== 0x17 && op !== 0x1b) || (op >= 0x20 && op <= 0x22)) {
      const b = st[sp - 1];
      const a = st[sp - 2];
      let r: number;
      if (op === 0x10) r = (a + b) | 0;
      else if (op === 0x11) r = (a - b) | 0;
      else if (op === 0x12) r = Math.imul(a, b);
      else if (op === 0x13) { if (b === 0) return done(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
      else if (op === 0x14) { if (b === 0) return done(4); r = b === -1 ? 0 : (a % b) | 0; }
      else if (op === 0x15) { if (b === 0) return done(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
      else if (op === 0x16) { if (b === 0) return done(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
      else if (op === 0x18) r = a & b;
      else if (op === 0x19) r = a | b;
      else if (op === 0x1a) r = a ^ b;
      else if (op === 0x1c) r = a << (b & 31);
      else if (op === 0x1d) r = a >> (b & 31);
      else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
      else if (op === 0x20) r = a === b ? 1 : 0;
      else if (op === 0x21) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      st[sp - 2] = r;
      sp--;
      continue;
    }

    switch (op) {
      case 0x00: return done(0);
      case 0x01: st[sp++] = (p[next - 1] << 24) >> 24; break;
      case 0x02:
        st[sp++] = p[next - 4] | (p[next - 3] << 8) | (p[next - 2] << 16) | (p[next - 1] << 24);
        break;
      case 0x03: sp--; break;
      case 0x04: st[sp] = st[sp - 1]; sp++; break;
      case 0x05: { const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; break; }
      case 0x06: st[sp] = st[sp - 2]; sp++; break;
      case 0x07: { const a = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a; break; }
      case 0x17: st[sp - 1] = (-st[sp - 1]) | 0; break;
      case 0x1b: st[sp - 1] = ~st[sp - 1]; break;
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[next - 2] | (p[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = st[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (csp === 64) return done(7);
        cs[csp++] = next;
        pc = p[next - 2] | (p[next - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return done(8);
        pc = cs[--csp];
        break;
      case 0x40: {
        const addr = st[sp - 1];
        if (addr < 0 || addr > 255) return done(6);
        st[sp - 1] = mem[addr];
        break;
      }
      case 0x41: {
        const addr = st[sp - 1];
        if (addr < 0 || addr > 255) return done(6);
        mem[addr] = st[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: {
        const s = String(st[sp - 1]);
        if (olen + s.length > 65536) return done(11);
        sp--;
        for (let i = 0; i < s.length; i++) buf[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (olen + 1 > 65536) return done(11);
        buf[olen++] = st[--sp] & 255;
        break;
      case 0x52: st[sp++] = inPos < inp.length ? inp[inPos++] : -1; break;
      case 0x53: return done(st[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  let inp: Uint8Array;
  try { inp = readFileSync(join(I, id, 'input.bin')); } catch { inp = new Uint8Array(0); }
  const { out, code } = run(readFileSync(join(I, id, 'program.bin')), inp);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), out);
  writeFileSync(join(O, id, 'exit.txt'), code + '\n');
}
