#!/usr/bin/env node

const fs = require('fs');
const path = require('path');
const prompts = require('prompts');
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
// init — install kit in current project (interactive)
// ---------------------------------------------------------------------------

// Tool config: which template file goes to which destination
const TOOL_CONFIGS = {
  claude: {
    label: 'Claude Code',
    description: 'reads .agent/ + .claude/commands/ (already inside .agent)',
    targets: [], // Claude is zero-config — handled by .agent copy itself
  },
  copilot: {
    label: 'GitHub Copilot Chat',
    description: 'writes .github/copilot-instructions.md',
    targets: [{ src: 'rules/copilot-instructions.md', dest: '.github/copilot-instructions.md' }],
  },
  gemini: {
    label: 'Gemini CLI',
    description: 'writes GEMINI.md',
    targets: [{ src: 'rules/GEMINI.md', dest: 'GEMINI.md' }],
  },
  cursor: {
    label: 'Cursor',
    description: 'writes .cursorrules',
    targets: [{ src: 'rules/cursorrules.md', dest: '.cursorrules' }],
  },
  antigravity: {
    label: 'Google Antigravity',
    description: 'writes AGENTS.md',
    targets: [{ src: 'rules/AGENTS.md', dest: 'AGENTS.md' }],
  },
};

const ALL_SKILLS = [
  'asic-flows', 'axi-protocols', 'brainstorming', 'clean-rtl',
  'clock-domain-crossing', 'dft-patterns', 'formal-verification', 'fpga-flows',
  'fsm-design', 'ip-reuse', 'low-power-design', 'plan-writing',
  'synthesis-guidelines', 'systemverilog-coding', 'tcl-scripting',
  'timing-constraints', 'uvm-coding', 'waveform-debugging',
];

const SKILL_DESCRIPTIONS = {
  'asic-flows': 'ASIC synthesis & implementation (Synopsys, Cadence)',
  'axi-protocols': 'AXI4, AXI-Lite, AXI-Stream protocols',
  'brainstorming': 'Architecture exploration, Socratic questioning',
  'clean-rtl': 'RTL coding standards and synthesizable patterns',
  'clock-domain-crossing': 'Synchronizers, async FIFO, handshake CDC ⭐',
  'dft-patterns': 'Scan, BIST, ATPG',
  'formal-verification': 'Assertions, properties, model checking',
  'fpga-flows': 'Vivado, Quartus workflows',
  'fsm-design': 'State machines, encoding, timeout patterns ⭐',
  'ip-reuse': 'IP packaging and portability',
  'low-power-design': 'UPF, power gating, clock gating',
  'plan-writing': 'Task breakdown and plan authoring',
  'synthesis-guidelines': 'Synthesis-friendly RTL, attributes, GLS ⭐',
  'systemverilog-coding': 'logic/reg/wire, interfaces, generate ⭐',
  'tcl-scripting': 'Tcl scripting for EDA tools',
  'timing-constraints': 'SDC/XDC clocks, I/O delays, exceptions ⭐',
  'uvm-coding': 'UVM 1.2 components, sequences, TLM, RAL ⭐',
  'waveform-debugging': 'Waveform analysis and debug techniques',
};

function parseFlagValue(flag) {
  // Support --flag=value and --flag value
  const idx = args.findIndex((a) => a === flag || a.startsWith(`${flag}=`));
  if (idx === -1) return null;
  if (args[idx].includes('=')) return args[idx].split('=').slice(1).join('=');
  return args[idx + 1] || null;
}

async function init(targetDir = '.') {
  const packageDir = path.dirname(__dirname);
  const agentSrc = path.join(packageDir, '.agent');
  const agentDest = path.join(targetDir, '.agent');

  const force = args.includes('--force');
  const yes = args.includes('-y') || args.includes('--yes');
  const toolsFlag = parseFlagValue('--tools');     // e.g. --tools=claude,copilot
  const skillsFlag = parseFlagValue('--skills');   // e.g. --skills=fsm-design,uvm-coding or 'all'

  log('\n🚀 VLSI Kit - AI Agent Kit for VLSI Development\n', COLORS.cyan + COLORS.bold);

  if (fs.existsSync(agentDest)) {
    log('⚠️  .agent directory already exists!', COLORS.yellow);
    if (!force) {
      log('   Use --force to overwrite.\n', COLORS.yellow);
      process.exit(1);
    }
    log('   Overwriting existing .agent directory...\n', COLORS.yellow);
    fs.rmSync(agentDest, { recursive: true, force: true });
  }

  // ---------- Step 1: tool selection (interactive checkbox list) ----------
  let selectedTools;
  if (toolsFlag) {
    selectedTools = toolsFlag === 'all'
      ? Object.keys(TOOL_CONFIGS)
      : toolsFlag.split(',').map((t) => t.trim()).filter((t) => TOOL_CONFIGS[t]);
  } else if (yes) {
    selectedTools = ['claude', 'copilot', 'gemini'];
  } else {
    const defaults = { claude: true, copilot: true, gemini: true, cursor: false, antigravity: false };
    const toolChoices = Object.entries(TOOL_CONFIGS).map(([key, cfg]) => ({
      title: cfg.label,
      description: cfg.description,
      value: key,
      selected: defaults[key],
    }));

    const result = await prompts({
      type: 'multiselect',
      name: 'tools',
      message: 'Which AI tools will you use?',
      choices: toolChoices,
      hint: '- Space to toggle. Enter to confirm. (a) toggle all',
      instructions: false,
    }, { onCancel: () => process.exit(1) });

    selectedTools = result.tools || [];
  }

  // ---------- Step 2: skill selection (interactive checkbox list) ----------
  let selectedSkills;
  if (skillsFlag) {
    selectedSkills = skillsFlag === 'all'
      ? ALL_SKILLS
      : skillsFlag.split(',').map((s) => s.trim()).filter((s) => ALL_SKILLS.includes(s));
  } else if (yes) {
    selectedSkills = ALL_SKILLS;
  } else {
    const skillChoices = ALL_SKILLS.map((s) => ({
      title: s,
      value: s,
      selected: true,   // all selected by default
      description: SKILL_DESCRIPTIONS[s] || '',
    }));

    const result = await prompts({
      type: 'multiselect',
      name: 'skills',
      message: 'Which skills do you want? (all selected)',
      choices: skillChoices,
      hint: '- Space to toggle. Enter to confirm. (a) toggle all',
      instructions: false,
    }, { onCancel: () => process.exit(1) });

    selectedSkills = result.skills || ALL_SKILLS;
    if (selectedSkills.length === 0) {
      log('No skills selected — defaulting to all 18.\n', COLORS.yellow);
      selectedSkills = ALL_SKILLS;
    }
  }

  // ---------- Step 3: copy files ----------
  log(`\n${COLORS.bold}Installing...${COLORS.reset}`, COLORS.cyan);

  // Copy .agent/ structure (always include agents, workflows, rules, _templates)
  log('📁 Copying agents, workflows, rules...');
  fs.mkdirSync(agentDest, { recursive: true });
  for (const sub of ['agents', 'workflows', 'rules', '_templates']) {
    const s = path.join(agentSrc, sub);
    if (fs.existsSync(s)) copyDir(s, path.join(agentDest, sub));
  }

  // Copy ARCHITECTURE.md
  const archSrc = path.join(agentSrc, 'ARCHITECTURE.md');
  if (fs.existsSync(archSrc)) {
    fs.copyFileSync(archSrc, path.join(agentDest, 'ARCHITECTURE.md'));
  }

  // Copy selected skills
  log(`📁 Copying ${selectedSkills.length} skill(s)...`);
  fs.mkdirSync(path.join(agentDest, 'skills'), { recursive: true });
  for (const skill of selectedSkills) {
    const s = path.join(agentSrc, 'skills', skill);
    if (fs.existsSync(s)) copyDir(s, path.join(agentDest, 'skills', skill));
  }

  // Write tool configs
  for (const tool of selectedTools) {
    for (const t of TOOL_CONFIGS[tool].targets) {
      const src = path.join(agentSrc, t.src);
      const dest = path.join(targetDir, t.dest);
      if (!fs.existsSync(src)) continue;
      if (fs.existsSync(dest)) {
        log(`   ${COLORS.gray}skip ${t.dest} (exists)${COLORS.reset}`);
        continue;
      }
      fs.mkdirSync(path.dirname(dest), { recursive: true });
      fs.copyFileSync(src, dest);
      log(`📄 ${t.dest}`);
    }
  }

  // ---------- Done ----------
  log(`\n✅ VLSI Kit initialized!\n`, COLORS.green + COLORS.bold);
  log('📦 Installed:', COLORS.cyan);
  log('   • 14 Specialist Agents');
  log(`   • ${selectedSkills.length} VLSI Skills${selectedSkills.length < 18 ? ` (${ALL_SKILLS.length - selectedSkills.length} skipped)` : ''}`);
  log('   • 10 Workflows');
  if (selectedTools.length) {
    log('\n📄 Tool configs:', COLORS.cyan);
    selectedTools.forEach((t) => log(`   ✓ ${TOOL_CONFIGS[t].label}`));
  }
  log('\n📖 Try it:', COLORS.cyan);
  log('   vlsi-agkit list            # browse skills, agents, workflows');
  log('   vlsi-agkit skill <name>    # read a skill from terminal');
  log('   vlsi-agkit search <query>  # search the kit\n');
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
  log('  init                        Interactive install (prompts for tools + skills)');
  log('  init --yes                  Non-interactive: defaults (Claude+Copilot+Gemini, all skills)');
  log('  init --tools=<list>         Comma-list of tools (claude,copilot,gemini,cursor,antigravity,all)');
  log('  init --skills=<list>        Comma-list of skill names or "all"');
  log('  init --force                Overwrite existing .agent/');
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
async function main() {
  switch (command) {
    case 'init':
      await init(args[1] && !args[1].startsWith('-') ? args[1] : '.');
      break;
    default:
      runSync();
  }
}

function runSync() {
switch (command) {
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
}

main().catch((e) => { err(e.message); process.exit(1); });
