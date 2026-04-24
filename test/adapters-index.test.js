const test = require('node:test');
const assert = require('node:assert');
const adapters = require('../bin/adapters');

test('registry exposes all six adapter ids', () => {
  const ids = adapters.list().map(a => a.id).sort();
  assert.deepStrictEqual(ids, [
    'antigravity', 'claude', 'cursor', 'gemini', 'vscode', 'windsurf'
  ]);
});

test('get(id) returns adapter', () => {
  assert.strictEqual(adapters.get('cursor').id, 'cursor');
});

test('get(unknown) throws with valid list', () => {
  assert.throws(() => adapters.get('nope'), /nope.*claude/s);
});

test('every adapter declares id, name, targetPaths, emit', () => {
  for (const a of adapters.list()) {
    assert.ok(a.id, `${a.id} has no id`);
    assert.ok(a.name, `${a.id} has no name`);
    assert.ok(Array.isArray(a.targetPaths), `${a.id} targetPaths not array`);
    assert.strictEqual(typeof a.emit, 'function', `${a.id} emit not function`);
  }
});
