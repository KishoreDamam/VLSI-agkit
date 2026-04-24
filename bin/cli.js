#!/usr/bin/env node

const fs = require('node:fs');
const path = require('node:path');
const profiles = require('./profiles');
const adaptersReg = require('./adapters');
const { pathExists } = require('./fs-util');
const {
  parseToolsCsv, validateNonInteractiveFlags,
  promptInteractive, promptOverwrite
} = require('./prompts');

const COLORS = { reset: '\x1b[0m', green: '\x1b[32m', cyan: '\x1b[36m',
  yellow: '\x1b[33m', red: '\x1b[31m', bold: '\x1b[1m' };
const log = (msg, color = '') => console.log(`${color}${msg}${COLORS.reset}`);

function parseArgs(argv) {
  const out = { command: null, role: null, tools: null, dir: '.',
    force: false, listProfiles: false, listTools: false };
  if (argv.length === 0) { out.command = 'help'; return out; }

  // First positional is command, unless it starts with "-"
  let i = 0;
  if (!argv[0].startsWith('-')) { out.command = argv[i++]; }

  for (; i < argv.length; i++) {
    const a = argv[i];
    switch (a) {
      case '--role':           out.role = argv[++i]; break;
      case '--tools':          out.tools = argv[++i]; break;
      case '--dir':            out.dir = argv[++i]; break;
      case '--force':          out.force = true; break;
      case '--list-profiles':  out.listProfiles = true; break;
      case '--list-tools':     out.listTools = true; break;
      case '-v':
      case '--version':        out.command = 'version'; break;
      case '-h':
      case '--help':           out.command = 'help'; break;
      default:
        if (a.startsWith('-')) throw new Error(`Unknown flag: ${a}`);
    }
  }
  return out;
}

function showHelp() {
  log('\nVLSI Agent Kit CLI\n', COLORS.cyan + COLORS.bold);
  log('Usage: vlsi-agkit <command> [options]\n');
  log('Commands:');
  log('  init [options]     Initialize VLSI Agent Kit');
  log('  help               Show this help');
  log('  version            Show version\n');
  log('Options (init):');
  log('  --role <id>        Profile id (skips prompt)');
  log('  --tools <csv>      Comma-separated tool ids (skips prompt)');
  log('  --dir <path>       Target directory (default: .)');
  log('  --force            Overwrite existing target paths');
  log('  --list-profiles    Print profiles and exit');
  log('  --list-tools       Print tools and exit\n');
}

function showVersion() {
  const pkg = require('../package.json');
  log(`VLSI Agent Kit v${pkg.version}`);
}

function listProfilesCmd() {
  log('\nAvailable role profiles:\n', COLORS.cyan + COLORS.bold);
  for (const p of profiles.list()) {
    log(`  ${p.id}`, COLORS.green);
    log(`    ${p.name} \u2014 ${p.description}`);
  }
  log('');
}

function listToolsCmd() {
  log('\nAvailable tools:\n', COLORS.cyan + COLORS.bold);
  for (const a of adaptersReg.list()) {
    log(`  ${a.id}`, COLORS.green);
    log(`    ${a.name} (writes: ${a.targetPaths.join(', ')})`);
  }
  log('');
}

async function init(opts) {
  log('\nVLSI Kit \u2014 AI Agent Kit for VLSI Development\n', COLORS.cyan + COLORS.bold);

  const interactive = process.stdin.isTTY && !opts.role && !opts.tools;

  let role, toolsIds, targetDir;
  if (interactive) {
    const ans = await promptInteractive({ defaultDir: opts.dir });
    role = ans.role; toolsIds = ans.tools; targetDir = ans.dir;
  } else {
    validateNonInteractiveFlags({ role: opts.role, tools: opts.tools });
    role = opts.role;
    toolsIds = parseToolsCsv(opts.tools);
    targetDir = opts.dir;
  }

  const packageDir = path.dirname(__dirname);
  const agentsDir = path.join(packageDir, '.agent/agents');
  const profile = profiles.resolve(role, agentsDir);
  const selected = toolsIds.map(id => adaptersReg.get(id));

  // Conflict pre-check
  const conflicts = [];
  for (const a of selected) {
    for (const rel of a.targetPaths) {
      const abs = path.join(targetDir, rel);
      if (pathExists(abs)) conflicts.push({ adapter: a.id, path: abs });
    }
  }

  if (conflicts.length > 0 && !opts.force) {
    if (interactive) {
      for (const c of conflicts) {
        const ok = await promptOverwrite(c.path);
        if (!ok) { log(`Aborted: ${c.path} not overwritten.`, COLORS.yellow); return 1; }
      }
      // Remove conflicted paths so adapters write cleanly
      for (const c of conflicts) fs.rmSync(c.path, { recursive: true, force: true });
    } else {
      log('Refusing to overwrite existing paths:', COLORS.red);
      for (const c of conflicts) log(`  ${c.path}`);
      log('Re-run with --force to overwrite.');
      return 1;
    }
  } else if (conflicts.length > 0 && opts.force) {
    for (const c of conflicts) fs.rmSync(c.path, { recursive: true, force: true });
  }

  // Emit
  log(`Profile: ${profile.name} (${profile.agents.length} agents, ${profile.skills.length} skills, ${profile.workflows.length} workflows)`, COLORS.cyan);
  for (const a of selected) {
    log(`Emitting for ${a.name}`, COLORS.cyan);
    a.emit({ profile, sourceDir: packageDir, targetDir, log: msg => log(msg), force: opts.force });
  }

  log('\nDone.\n', COLORS.green + COLORS.bold);
  return 0;
}

async function main(argv) {
  let opts;
  try { opts = parseArgs(argv); }
  catch (e) { log(`Error: ${e.message}`, COLORS.red); process.exit(1); }

  try {
    switch (opts.command) {
      case 'init':
        if (opts.listProfiles) { listProfilesCmd(); return; }
        if (opts.listTools)    { listToolsCmd(); return; }
        process.exit(await init(opts));
        break;
      case 'version': showVersion(); break;
      case 'help':
      default:        showHelp(); break;
    }
  } catch (e) {
    log(`Error: ${e.message}`, COLORS.red);
    process.exit(1);
  }
}

module.exports = { parseArgs, main };

if (require.main === module) {
  main(process.argv.slice(2));
}
