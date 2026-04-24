const test = require('node:test');
const assert = require('node:assert');
const { execFileSync } = require('node:child_process');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');

const CLI = path.join(__dirname, '../bin/cli.js');

function runCli(args, cwd) {
  try {
    return execFileSync(process.execPath, [CLI, ...args], {
      cwd, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe']
    });
  } catch (e) {
    // Node's execFileSync puts stderr on e.stderr; surface it in the
    // message so assert.throws regexes can match CLI error output.
    if (e.stderr) e.message += '\n' + e.stderr;
    if (e.stdout) e.message += '\n' + e.stdout;
    throw e;
  }
}

test('init --role full-stack --tools antigravity writes .agent/', () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'it-'));
  runCli(['init', '--role', 'full-stack', '--tools', 'antigravity', '--dir', dir], process.cwd());
  assert.ok(fs.existsSync(path.join(dir, '.agent/agents/rtl-designer.md')));
});

test('init with all tools and fpga-engineer profile', () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'it-'));
  runCli(['init',
    '--role', 'fpga-engineer',
    '--tools', 'claude,gemini,vscode,antigravity,cursor,windsurf',
    '--dir', dir
  ], process.cwd());

  assert.ok(fs.existsSync(path.join(dir, '.claude/agents/fpga-specialist.md')));
  assert.ok(fs.existsSync(path.join(dir, 'GEMINI.md')));
  assert.ok(fs.existsSync(path.join(dir, '.github/copilot-instructions.md')));
  assert.ok(fs.existsSync(path.join(dir, '.agent/agents/fpga-specialist.md')));
  assert.ok(fs.existsSync(path.join(dir, '.cursor/rules/fpga-specialist.mdc')));
  assert.ok(fs.existsSync(path.join(dir, '.windsurf/rules/fpga-specialist.md')));

  // Filtered out: verification-engineer not in fpga-engineer profile
  assert.ok(!fs.existsSync(path.join(dir, '.claude/agents/verification-engineer.md')));
});

test('init refuses to overwrite without --force', () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'it-'));
  fs.mkdirSync(path.join(dir, '.agent'));
  assert.throws(() => runCli([
    'init', '--role', 'full-stack', '--tools', 'antigravity', '--dir', dir
  ], process.cwd()), /Refusing to overwrite|non-zero/);
});

test('init --force overwrites', () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'it-'));
  fs.mkdirSync(path.join(dir, '.agent'));
  fs.writeFileSync(path.join(dir, '.agent/stale.txt'), 'old');
  runCli(['init', '--role', 'full-stack', '--tools', 'antigravity',
          '--dir', dir, '--force'], process.cwd());
  assert.ok(!fs.existsSync(path.join(dir, '.agent/stale.txt')),
    'stale file removed');
  assert.ok(fs.existsSync(path.join(dir, '.agent/agents/rtl-designer.md')));
});

test('init --list-profiles exits 0 and prints ids', () => {
  const out = runCli(['init', '--list-profiles'], process.cwd());
  assert.ok(out.includes('full-stack'));
  assert.ok(out.includes('fpga-engineer'));
});

test('init without role/tools in non-TTY fails with guidance', () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'it-'));
  assert.throws(() => runCli(['init', '--dir', dir], process.cwd()),
    /non-zero|--role/);
});
