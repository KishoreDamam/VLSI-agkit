const claude = require('./claude');
const gemini = require('./gemini');
const vscode = require('./vscode');
const antigravity = require('./antigravity');
const cursor = require('./cursor');
const windsurf = require('./windsurf');

const ALL = [claude, gemini, vscode, antigravity, cursor, windsurf];
const BY_ID = Object.fromEntries(ALL.map(a => [a.id, a]));
const VALID_IDS = new Set(ALL.map(a => a.id));

function list() { return ALL.slice(); }
function get(id) {
  if (!BY_ID[id]) {
    throw new Error(`Unknown tool "${id}". Valid: ${[...VALID_IDS].join(', ')}`);
  }
  return BY_ID[id];
}
module.exports = { list, get, VALID_IDS };
