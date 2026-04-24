const test = require('node:test');
const assert = require('node:assert');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const { readFrontmatter, pathExists, writeFile, copyDir } = require('../bin/fs-util');

function tmpFile(contents) {
  const p = path.join(fs.mkdtempSync(path.join(os.tmpdir(), 'fsu-')), 'f.md');
  fs.writeFileSync(p, contents);
  return p;
}

test('readFrontmatter parses flat scalars', () => {
  const p = tmpFile('---\nname: foo\ndescription: a thing\n---\n# Body\nhello');
  const { data, body } = readFrontmatter(p);
  assert.strictEqual(data.name, 'foo');
  assert.strictEqual(data.description, 'a thing');
  assert.strictEqual(body.trim(), '# Body\nhello');
});

test('readFrontmatter keeps scalars literal (commas not auto-split)', () => {
  // Real agent descriptions contain commas; the parser MUST NOT auto-split.
  // Callers decide whether a specific key is a list and split themselves.
  const p = tmpFile('---\nskills: a, b , c\ndescription: Expert in A, B, and C.\n---\nbody');
  const { data } = readFrontmatter(p);
  assert.strictEqual(data.skills, 'a, b , c');
  assert.strictEqual(data.description, 'Expert in A, B, and C.');
});

test('readFrontmatter returns empty data when no frontmatter', () => {
  const p = tmpFile('# Just a heading\nno fm');
  const { data, body } = readFrontmatter(p);
  assert.deepStrictEqual(data, {});
  assert.ok(body.includes('Just a heading'));
});

test('readFrontmatter throws on nested mapping', () => {
  const p = tmpFile('---\nnested:\n  key: v\n---\n');
  assert.throws(() => readFrontmatter(p), /not supported/i);
});

test('readFrontmatter throws on unclosed fence', () => {
  const p = tmpFile('---\nname: x\n# no closing fence');
  assert.throws(() => readFrontmatter(p), /unclosed/i);
});

test('pathExists returns true/false', () => {
  const d = fs.mkdtempSync(path.join(os.tmpdir(), 'pe-'));
  assert.strictEqual(pathExists(d), true);
  assert.strictEqual(pathExists(path.join(d, 'nope')), false);
});

test('writeFile creates parent dirs', () => {
  const d = fs.mkdtempSync(path.join(os.tmpdir(), 'wf-'));
  const target = path.join(d, 'a/b/c.txt');
  writeFile(target, 'hi');
  assert.strictEqual(fs.readFileSync(target, 'utf8'), 'hi');
});

test('copyDir recursively copies', () => {
  const src = fs.mkdtempSync(path.join(os.tmpdir(), 'cs-'));
  const dst = fs.mkdtempSync(path.join(os.tmpdir(), 'cd-'));
  fs.mkdirSync(path.join(src, 'sub'));
  fs.writeFileSync(path.join(src, 'a.txt'), 'A');
  fs.writeFileSync(path.join(src, 'sub/b.txt'), 'B');
  copyDir(src, path.join(dst, 'out'));
  assert.strictEqual(fs.readFileSync(path.join(dst, 'out/a.txt'), 'utf8'), 'A');
  assert.strictEqual(fs.readFileSync(path.join(dst, 'out/sub/b.txt'), 'utf8'), 'B');
});
