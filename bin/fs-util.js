const fs = require('node:fs');
const path = require('node:path');

function pathExists(p) {
  try { fs.accessSync(p); return true; } catch { return false; }
}

function writeFile(target, contents) {
  fs.mkdirSync(path.dirname(target), { recursive: true });
  fs.writeFileSync(target, contents);
}

function copyFile(src, dst) {
  fs.mkdirSync(path.dirname(dst), { recursive: true });
  fs.copyFileSync(src, dst);
}

function copyDir(src, dst) {
  fs.mkdirSync(dst, { recursive: true });
  for (const entry of fs.readdirSync(src, { withFileTypes: true })) {
    const s = path.join(src, entry.name);
    const d = path.join(dst, entry.name);
    if (entry.isDirectory()) copyDir(s, d);
    else fs.copyFileSync(s, d);
  }
}

// Minimal frontmatter parser. Supports:
//   flat scalars: `key: value` — value kept as literal string (NOT split on commas)
// Callers that want a list-valued key (e.g., `skills`) must split the string
// themselves. This is intentional: agent `description:` fields contain commas
// as ordinary prose.
// Throws on nested mappings, block scalars, unclosed fences.
function readFrontmatter(filePath) {
  const raw = fs.readFileSync(filePath, 'utf8');
  const lines = raw.split(/\r?\n/);
  if (lines[0] !== '---') return { data: {}, body: raw };

  let end = -1;
  for (let i = 1; i < lines.length; i++) {
    if (lines[i] === '---') { end = i; break; }
  }
  if (end === -1) {
    throw new Error(`readFrontmatter: unclosed --- fence in ${filePath}`);
  }

  const data = {};
  for (let i = 1; i < end; i++) {
    const line = lines[i];
    if (line.trim() === '') continue;
    const m = line.match(/^([A-Za-z0-9_-]+):\s*(.*)$/);
    if (!m) {
      throw new Error(`readFrontmatter: not supported (unparseable line "${line}") in ${filePath}`);
    }
    const key = m[1];
    const rhs = m[2].trim();
    if (rhs === '') {
      // "key:" with value on subsequent indented lines = nested mapping / block scalar
      const next = lines[i + 1] || '';
      if (/^\s+\S/.test(next)) {
        throw new Error(`readFrontmatter: nested structures not supported (key "${key}") in ${filePath}`);
      }
      data[key] = '';
      continue;
    }
    data[key] = rhs;
  }

  const body = lines.slice(end + 1).join('\n');
  return { data, body };
}

module.exports = { pathExists, writeFile, copyFile, copyDir, readFrontmatter };
