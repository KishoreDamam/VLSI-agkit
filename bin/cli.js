#!/usr/bin/env node

const fs = require('fs');
const path = require('path');
const { spawnSync } = require('child_process');

const args = process.argv.slice(2);
const command = args[0];

const COLORS = {
  reset: '\x1b[0m',
  green: '\x1b[32m',
  cyan: '\x1b[36m',
  yellow: '\x1b[33m',
  red: '\x1b[31m',
  gray: '\x1b[90m',
  bold: '\x1b[1m',
};

function log(msg, color = '') {
  console.log(`${color}${msg}${COLORS.reset}`);
}

function err(msg) {
  console.error(`${COLORS.red}error:${COLORS.reset} ${msg}`);
}

function copyDir(src, dest) {
  fs.mkdirSync(dest, { recursive: true });
  const entries = fs.readdirSync(src, { withFileTypes: true });

  for (const entry of entries) {
    const srcPath = path.join(src, entry.name);
    const destPath = path.join(dest, entry.name);

    if (entry.isDirectory()) {
      copyDir(srcPath, destPath);
    } else {
      fs.copyFileSync(srcPath, destPath);
    }
  }
}

// Find .agent root: prefer cwd's .agent, fall back to bundled .agent in npm package
function findAgentRoot() {
  const cwdAgent = path.join(process.cwd(), '.agent');
  if (fs.existsSync(cwdAgent)) return { root: cwdAgent, source: 'cwd' };

  const packageAgent = path.join(path.dirname(__dirname), '.agent');
  if (fs.existsSync(packageAgent)) return { root: packageAgent, source: 'package' };

  return null;
}

function listDir(dir, opts = {}) {
  if (!fs.existsSync(dir)) return [];
  return fs.readdirSync(dir, { withFileTypes: true })
    .filter((e) => {
      if (e.name.startsWith('_')) return false;
      if (opts.dirsOnly) return e.isDirectory();
      if (opts.filesOnly) return e.isFile();
      return true;
    })
    .map((e) => e.name)
    .sort();
}

function readFrontmatter(filePath) {
  if (!fs.existsSync(filePath)) return null;
  const content = fs.readFileSync(filePath, 'utf8');
  const match = content.match(/^---\n([\s\S]*?)\n---/);
  if (!match) return null;
  const fm = {};
  match[1].split('\n').forEach((line) => {
    const m = line.match(/^([^:]+):\s*(.+?)\s*$/);
    if (m) fm[m[1].trim()] = m[2].replace(/^["']|["']$/g, '');
  });
  return fm;
}

// ---------------------------------------------------------------------------
// init — install kit in current project
// ---------------------------------------------------------------------------
function init(targetDir = '.') {
  const packageDir = path.dirname(__dirname);
  const agentSrc = path.join(packageDir, '.agent');
  const agentDest = path.join(targetDir, '.agent');

  log('\n🚀 VLSI Kit - AI Agent Kit for VLSI Development\n', COLORS.cyan + COLORS.bold);

  if (fs.existsSync(agentDest)) {
    log('⚠️  .agent directory already exists!', COLORS.yellow);
    log('   Use --force to overwrite.\n', COLORS.yellow);

    if (!args.includes('--force')) {
      process.exit(1);
    }
    log('   Overwriting existing .agent directory...\n', COLORS.yellow);
    fs.rmSync(agentDest, { recursive: true, force: true });
  }

  log('📁 Copying VLSI agent files...', COLORS.cyan);
  copyDir(agentSrc, agentDest);

  const geminiSrc = path.join(agentSrc, 'rules', 'GEMINI.md');
  const geminiDest = path.join(targetDir, 'GEMINI.md');
  if (!fs.existsSync(geminiDest)) {
    log('📄 Creating GEMINI.md in project root...', COLORS.cyan);
    fs.copyFileSync(geminiSrc, geminiDest);
  }

  const copilotSrc = path.join(agentSrc, 'rules', 'copilot-instructions.md');
  const githubDir = path.join(targetDir, '.github');
  const copilotDest = path.join(githubDir, 'copilot-instructions.md');
  if (fs.existsSync(copilotSrc) && !fs.existsSync(copilotDest)) {
    log('📄 Creating .github/copilot-instructions.md...', COLORS.cyan);
    fs.mkdirSync(githubDir, { recursive: true });
    fs.copyFileSync(copilotSrc, copilotDest);
  }

  log('\n✅ VLSI Kit initialized successfully!\n', COLORS.green + COLORS.bold);
  log('📦 Installed:', COLORS.cyan);
  log('   • 14 Specialist Agents');
  log('   • 18 VLSI Skills');
  log('   • 10 Workflows');
  log('   • GEMINI.md (Gemini CLI)');
  log('   • .github/copilot-instructions.md (GitHub Copilot Chat)\n');
  log('📖 Next steps:', COLORS.cyan);
  log('   vlsi-agkit list            # browse skills, agents, workflows');
  log('   vlsi-agkit skill <name>    # read a skill from terminal');
  log('   vlsi-agkit search <query>  # search the kit');
  log('   vlsi-agkit verify          # run skill examples (needs make + sim)\n');
}

// ---------------------------------------------------------------------------
// list — list skills, agents, workflows
// ---------------------------------------------------------------------------
function listCmd(filter) {
  const a = findAgentRoot();
  if (!a) {
    err('no .agent/ found in cwd and no bundled kit found. Run `vlsi-agkit init` first.');
    process.exit(1);
  }

  const sections = {
    skills: { dir: path.join(a.root, 'skills'), describe: skillDesc, opts: { dirsOnly: true } },
    agents: { dir: path.join(a.root, 'agents'), describe: agentDesc, opts: { filesOnly: true } },
    workflows: { dir: path.join(a.root, 'workflows'), describe: workflowDesc, opts: { filesOnly: true } },
  };

  const want = filter ? [filter] : Object.keys(sections);

  log(`\n📁 VLSI Kit (source: ${a.source}) — ${a.root}\n`, COLORS.cyan + COLORS.bold);

  for (const key of want) {
    const sec = sections[key];
    if (!sec) {
      err(`unknown category '${key}'. Use one of: skills, agents, workflows`);
      process.exit(1);
    }
    const items = listDir(sec.dir, sec.opts);
    log(`${COLORS.bold}${key.toUpperCase()} (${items.length})${COLORS.reset}`, COLORS.green);
    for (const item of items) {
      const name = item.replace(/\.md$/, '');
      const desc = sec.describe(sec.dir, item);
      log(`  ${name.padEnd(28)} ${COLORS.gray}${desc || ''}${COLORS.reset}`);
    }
    log('');
  }
}

function skillDesc(dir, name) {
  const fm = readFrontmatter(path.join(dir, name, 'SKILL.md'));
  return fm ? fm.description || `[${fm.type || 'skill'}]` : '';
}
function agentDesc(dir, name) {
  const fm = readFrontmatter(path.join(dir, name));
  return fm ? (fm.description || '').slice(0, 80) : '';
}
function workflowDesc(dir, name) {
  const file = path.join(dir, name);
  if (!fs.existsSync(file)) return '';
  const content = fs.readFileSync(file, 'utf8');
  const match = content.match(/^#\s*(.+)$/m);
  return match ? match[1] : '';
}

// ---------------------------------------------------------------------------
// skill — print SKILL.md or a reference
// ---------------------------------------------------------------------------
function skillCmd(skillName, ref) {
  if (!skillName) {
    err('usage: vlsi-agkit skill <name> [<reference>]');
    process.exit(1);
  }
  const a = findAgentRoot();
  if (!a) { err('no kit found. Run `vlsi-agkit init`.'); process.exit(1); }

  const skillDir = path.join(a.root, 'skills', skillName);
  if (!fs.existsSync(skillDir)) {
    err(`skill '${skillName}' not found.`);
    log(`Available: ${listDir(path.join(a.root, 'skills'), { dirsOnly: true }).join(', ')}`, COLORS.gray);
    process.exit(1);
  }

  if (!ref) {
    // Print SKILL.md
    const skillFile = path.join(skillDir, 'SKILL.md');
    process.stdout.write(fs.readFileSync(skillFile, 'utf8'));
    return;
  }

  if (ref === '--list' || ref === '-l') {
    const refDir = path.join(skillDir, 'references');
    const exDir = path.join(skillDir, 'examples');
    log(`\n${COLORS.bold}${skillName}${COLORS.reset}\n`, COLORS.green);
    if (fs.existsSync(refDir)) {
      log('References:', COLORS.cyan);
      listDir(refDir, { filesOnly: true }).forEach((f) => log(`  ${f.replace(/\.md$/, '')}`));
    }
    if (fs.existsSync(exDir)) {
      log('\nExamples:', COLORS.cyan);
      listDir(exDir, { filesOnly: true }).forEach((f) => log(`  ${f}`));
    }
    log('');
    return;
  }

  // Print specific reference
  const refFile = path.join(skillDir, 'references', ref.endsWith('.md') ? ref : `${ref}.md`);
  if (!fs.existsSync(refFile)) {
    err(`reference '${ref}' not found in skill '${skillName}'.`);
    log(`Try: vlsi-agkit skill ${skillName} --list`, COLORS.gray);
    process.exit(1);
  }
  process.stdout.write(fs.readFileSync(refFile, 'utf8'));
}

// ---------------------------------------------------------------------------
// agent / workflow — print agent or workflow definition
// ---------------------------------------------------------------------------
function printDoc(category, name) {
  if (!name) {
    err(`usage: vlsi-agkit ${category} <name>`);
    process.exit(1);
  }
  const a = findAgentRoot();
  if (!a) { err('no kit found. Run `vlsi-agkit init`.'); process.exit(1); }

  const file = path.join(a.root, category, name.endsWith('.md') ? name : `${name}.md`);
  if (!fs.existsSync(file)) {
    err(`${category.replace(/s$/, '')} '${name}' not found.`);
    log(`Available: ${listDir(path.join(a.root, category), { filesOnly: true }).map((f) => f.replace(/\.md$/, '')).join(', ')}`, COLORS.gray);
    process.exit(1);
  }
  process.stdout.write(fs.readFileSync(file, 'utf8'));
}

// ---------------------------------------------------------------------------
// search — grep across the kit
// ---------------------------------------------------------------------------
function searchCmd(query) {
  if (!query) {
    err('usage: vlsi-agkit search <query>');
    process.exit(1);
  }
  const a = findAgentRoot();
  if (!a) { err('no kit found. Run `vlsi-agkit init`.'); process.exit(1); }

  const re = new RegExp(query, 'i');
  let total = 0;

  function walk(dir) {
    if (!fs.existsSync(dir)) return;
    for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
      if (entry.name.startsWith('_')) continue;
      const full = path.join(dir, entry.name);
      if (entry.isDirectory()) walk(full);
      else if (entry.name.endsWith('.md') || entry.name.endsWith('.sv')) {
        const content = fs.readFileSync(full, 'utf8');
        const lines = content.split('\n');
        const hits = [];
        lines.forEach((line, i) => {
          if (re.test(line)) hits.push({ n: i + 1, line: line.trim() });
        });
        if (hits.length) {
          const rel = path.relative(a.root, full);
          log(`\n${COLORS.cyan}${rel}${COLORS.reset}`);
          hits.slice(0, 5).forEach((h) => log(`  ${COLORS.gray}${h.n}${COLORS.reset}: ${h.line.slice(0, 120)}`));
          if (hits.length > 5) log(`  ${COLORS.gray}... and ${hits.length - 5} more${COLORS.reset}`);
          total += hits.length;
        }
      }
    }
  }

  walk(a.root);
  log(`\n${COLORS.bold}${total} match(es) for "${query}"${COLORS.reset}\n`);
}

// ---------------------------------------------------------------------------
// verify — run make verify on the kit (or one skill)
// ---------------------------------------------------------------------------
function verifyCmd(skillName) {
  const a = findAgentRoot();
  if (!a) { err('no kit found. Run `vlsi-agkit init`.'); process.exit(1); }
  if (a.source === 'package') {
    err('verify requires a project-level kit. Run `vlsi-agkit init` in your project first.');
    process.exit(1);
  }

  // The repo root Makefile lives one level above .agent/
  const projectRoot = path.dirname(a.root);
  const target = skillName ? `verify-${skillName}` : 'verify';

  log(`\n🔧 Running: make ${target}\n`, COLORS.cyan);
  const result = spawnSync('make', [target], { cwd: projectRoot, stdio: 'inherit', shell: true });
  process.exit(result.status || 0);
}

// ---------------------------------------------------------------------------
// help
// ---------------------------------------------------------------------------
function showHelp() {
  log('\n🔧 VLSI Agent Kit CLI\n', COLORS.cyan + COLORS.bold);
  log('Browse and use VLSI skills, agents, and workflows from the terminal.\n');
  log(`${COLORS.bold}Usage:${COLORS.reset} vlsi-agkit <command> [args]\n`);
  log(`${COLORS.bold}Setup:${COLORS.reset}`);
  log('  init [--force]              Install the kit in the current project');
  log('  version                     Print version\n');
  log(`${COLORS.bold}Browse:${COLORS.reset}`);
  log('  list [skills|agents|workflows]');
  log('                              List items in the kit');
  log('  skill <name>                Print a skill\'s SKILL.md');
  log('  skill <name> --list         List a skill\'s references and examples');
  log('  skill <name> <reference>    Print a specific reference doc');
  log('  agent <name>                Print an agent definition');
  log('  workflow <name>             Print a workflow procedure');
  log('  search <query>              Search the kit (case-insensitive regex)\n');
  log(`${COLORS.bold}Run:${COLORS.reset}`);
  log('  verify [skill]              Run make verify on the kit (needs sim)\n');
  log(`${COLORS.bold}Examples:${COLORS.reset}`);
  log(`  ${COLORS.gray}# Inside any project (no AI tool required):${COLORS.reset}`);
  log('  npx @kishore-damam/vlsi-agkit list skills');
  log('  npx @kishore-damam/vlsi-agkit skill clock-domain-crossing');
  log('  npx @kishore-damam/vlsi-agkit skill timing-constraints multicycle-paths');
  log('  npx @kishore-damam/vlsi-agkit search "async FIFO"');
  log('  npx @kishore-damam/vlsi-agkit agent rtl-designer');
  log('  npx @kishore-damam/vlsi-agkit workflow design');
  log('  npx @kishore-damam/vlsi-agkit verify fsm-design\n');
  log(`${COLORS.bold}Tips:${COLORS.reset}`);
  log('  • Pipe skill output to a pager:    vlsi-agkit skill uvm-coding | less');
  log('  • Save a skill to a file:          vlsi-agkit skill fsm-design > fsm.md');
  log('  • View raw markdown in glow/bat:   vlsi-agkit skill cdc | glow -\n');
}

function showVersion() {
  const pkg = require('../package.json');
  log(`vlsi-agkit v${pkg.version}`);
}

// ---------------------------------------------------------------------------
// main
// ---------------------------------------------------------------------------
switch (command) {
  case 'init':
    init(args[1] && !args[1].startsWith('-') ? args[1] : '.');
    break;
  case 'list':
  case 'ls':
    listCmd(args[1]);
    break;
  case 'skill':
    skillCmd(args[1], args[2]);
    break;
  case 'agent':
    printDoc('agents', args[1]);
    break;
  case 'workflow':
    printDoc('workflows', args[1]);
    break;
  case 'search':
  case 'grep':
    searchCmd(args.slice(1).join(' '));
    break;
  case 'verify':
    verifyCmd(args[1]);
    break;
  case 'version':
  case '-v':
  case '--version':
    showVersion();
    break;
  case 'help':
  case '-h':
  case '--help':
  case undefined:
    showHelp();
    break;
  default:
    err(`unknown command: ${command}`);
    log('Run `vlsi-agkit help` to see available commands.\n', COLORS.gray);
    process.exit(1);
}
