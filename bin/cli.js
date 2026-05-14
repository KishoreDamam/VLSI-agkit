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
  const match = content.match(/^---\r?\n([\s\S]*?)\r?\n---/);
  if (!match) return null;
  const fm = {};
  match[1].split(/\r?\n/).forEach((line) => {
    const m = line.match(/^([^:]+):\s*(.+?)\s*$/);
    if (m) fm[m[1].trim()] = m[2].replace(/^["']|["']$/g, '');
  });
  return fm;
}

// ---------------------------------------------------------------------------
// init — install kit in current project (interactive)
// ---------------------------------------------------------------------------

// Each tool gets a self-contained install at its native location.
// No `.agent/` is written to the user's project — bundled `.agent/`
// inside the npm package keeps `vlsi-agkit` CLI working as a fallback.
const TOOL_CONFIGS = {
  claude: {
    label: 'Claude Code',
    description: 'writes .claude/{skills,agents,commands}/',
  },
  copilot: {
    label: 'GitHub Copilot',
    description: 'writes .github/{copilot-instructions.md,skills/<name>/SKILL.md,prompts/}',
  },
  gemini: {
    label: 'Gemini CLI',
    description: 'writes GEMINI.md + .gemini/{skills,agents,workflows}/',
  },
  cursor: {
    label: 'Cursor',
    description: 'writes .cursor/rules/*.mdc',
  },
  antigravity: {
    label: 'Google Antigravity',
    description: 'writes AGENTS.md + .agents/{skills,workflows}/',
  },
};

const ALL_SKILLS = [
  'axi-protocols', 'brainstorming', 'cadence-flow', 'clean-rtl',
  'clock-domain-crossing', 'dft-patterns', 'formal-verification',
  'fsm-design', 'ip-reuse', 'low-power-design', 'plan-writing',
  'quartus-flow', 'sta', 'synopsys-flow', 'synthesis-guidelines',
  'systemverilog-coding', 'tcl-scripting', 'timing-constraints',
  'uvm-coding', 'vivado-flow', 'waveform-debugging',
];

// Read role -> skills mapping from agent frontmatter at runtime.
// Returns { rtl-designer: { description, skills: [...] }, ... }
function readRoles() {
  const packageDir = path.dirname(__dirname);
  const agentDir = path.join(packageDir, '.agent', 'agents');
  const roles = {};
  if (!fs.existsSync(agentDir)) return roles;
  for (const file of fs.readdirSync(agentDir)) {
    if (!file.endsWith('.md')) continue;
    const fm = readFrontmatter(path.join(agentDir, file));
    if (!fm) continue;
    const role = file.replace(/\.md$/, '');
    const skills = (fm.skills || '').split(',').map((s) => s.trim()).filter(Boolean);
    roles[role] = {
      description: fm.description || '',
      skills,
    };
  }
  return roles;
}

// First-sentence summary, truncated for picker hint
function shortDesc(s, max = 70) {
  if (!s) return '';
  const firstSentence = s.split(/[.!?](\s|$)/)[0];
  return firstSentence.length > max ? firstSentence.slice(0, max - 1) + '…' : firstSentence;
}

// Union of skills required by a set of roles, filtered to ALL_SKILLS
function unionSkills(roles, ROLES) {
  const set = new Set();
  for (const r of roles) {
    if (!ROLES[r]) continue;
    ROLES[r].skills.forEach((s) => set.add(s));
  }
  return Array.from(set).filter((s) => ALL_SKILLS.includes(s));
}

function parseFlagValue(flag) {
  // Support --flag=value and --flag value
  const idx = args.findIndex((a) => a === flag || a.startsWith(`${flag}=`));
  if (idx === -1) return null;
  if (args[idx].includes('=')) return args[idx].split('=').slice(1).join('=');
  return args[idx + 1] || null;
}

// ---------------------------------------------------------------------------
// Frontmatter helpers — split, parse, rewrite per tool
// ---------------------------------------------------------------------------

function splitFrontmatter(content) {
  const m = content.match(/^---\r?\n([\s\S]*?)\r?\n---\r?\n([\s\S]*)$/);
  if (!m) return { fm: {}, body: content };
  const fm = {};
  m[1].split(/\r?\n/).forEach((line) => {
    const mm = line.match(/^([^:]+):\s*(.*)$/);
    if (mm) fm[mm[1].trim()] = mm[2].trim().replace(/^["']|["']$/g, '');
  });
  return { fm, body: m[2] };
}

function fmYaml(obj) {
  const lines = ['---'];
  for (const [k, v] of Object.entries(obj)) {
    if (v === undefined || v === null) continue;
    if (typeof v === 'boolean') { lines.push(`${k}: ${v}`); continue; }
    const s = String(v);
    // Quote anything that isn't a plain word/sentence (has YAML-significant chars)
    const needsQuote = /[:#"'`*&!|>%@]/.test(s) || s.startsWith('-') || s === '';
    lines.push(`${k}: ${needsQuote ? JSON.stringify(s) : s}`);
  }
  lines.push('---', '');
  return lines.join('\n');
}

function readFile(p) {
  return fs.readFileSync(p, 'utf8');
}

function writeFile(p, content) {
  fs.mkdirSync(path.dirname(p), { recursive: true });
  fs.writeFileSync(p, content);
}

// ---------------------------------------------------------------------------
// Per-tool installers — each writes a self-contained kit for one tool
// ---------------------------------------------------------------------------

const ALL_WORKFLOWS = [
  'brainstorm', 'debug', 'design', 'integrate', 'lint',
  'plan', 'review', 'sta', 'synthesize', 'verify',
];

// Read raw skill files (SKILL.md + references/* + examples/*) for a skill
function loadSkill(agentSrc, skill) {
  const dir = path.join(agentSrc, 'skills', skill);
  const skillFile = path.join(dir, 'SKILL.md');
  if (!fs.existsSync(skillFile)) return null;
  const { fm, body } = splitFrontmatter(readFile(skillFile));
  // Collect all auxiliary files (references/, examples/)
  const aux = [];
  for (const sub of ['references', 'examples']) {
    const subDir = path.join(dir, sub);
    if (!fs.existsSync(subDir)) continue;
    for (const f of listDir(subDir, { filesOnly: true })) {
      aux.push({ relPath: path.join(sub, f), content: readFile(path.join(subDir, f)) });
    }
  }
  return { name: skill, fm, body, aux };
}

function loadAgent(agentSrc, role) {
  const file = path.join(agentSrc, 'agents', `${role}.md`);
  if (!fs.existsSync(file)) return null;
  const { fm, body } = splitFrontmatter(readFile(file));
  return { name: role, fm, body };
}

function loadWorkflow(agentSrc, name) {
  const file = path.join(agentSrc, 'workflows', `${name}.md`);
  if (!fs.existsSync(file)) return null;
  const { fm, body } = splitFrontmatter(readFile(file));
  return { name, fm, body };
}

// ---- Claude Code: .claude/{skills,agents,commands}/ ----
function installClaude(agentSrc, targetDir, roles, skills) {
  const base = path.join(targetDir, '.claude');
  let count = 0;
  for (const skill of skills) {
    const s = loadSkill(agentSrc, skill);
    if (!s) continue;
    const out = fmYaml({ name: s.fm.name || s.name, description: s.fm.description || '' }) + s.body;
    writeFile(path.join(base, 'skills', s.name, 'SKILL.md'), out);
    for (const a of s.aux) {
      writeFile(path.join(base, 'skills', s.name, a.relPath), a.content);
    }
    count++;
  }
  for (const role of roles) {
    const a = loadAgent(agentSrc, role);
    if (!a) continue;
    const out = fmYaml({ name: a.fm.name || a.name, description: a.fm.description || '' }) + a.body;
    writeFile(path.join(base, 'agents', `${a.name}.md`), out);
  }
  for (const wf of ALL_WORKFLOWS) {
    const w = loadWorkflow(agentSrc, wf);
    if (!w) continue;
    const out = fmYaml({ description: w.fm.description || '' }) + w.body;
    writeFile(path.join(base, 'commands', `${w.name}.md`), out);
  }
  return { dir: '.claude/', skills: count };
}

// ---- GitHub Copilot: .github/{skills,prompts}/ (cloud-agent skills spec) ----
// Conforms to https://docs.github.com/en/copilot/how-tos/copilot-on-github/customize-copilot/customize-cloud-agent/add-skills
function installCopilot(agentSrc, targetDir, roles, skills) {
  const base = path.join(targetDir, '.github');

  // Top-level routing index (informational; not a skill itself)
  const idx = [
    '# VLSI Kit — Copilot routing',
    '',
    'This project uses the VLSI Agent Kit. Cloud-agent skills live in `.github/skills/<name>/SKILL.md`.',
    'Slash-style workflow prompts are in `.github/prompts/`.',
    '',
    '## Roles installed (as skills)',
    '',
    ...roles.map((r) => `- \`agent-${r}\``),
    '',
    '## Skills installed',
    '',
    ...skills.map((s) => `- \`${s}\``),
    '',
    '## Workflow prompts',
    '',
    ...ALL_WORKFLOWS.map((w) => `- \`/${w}\``),
    '',
  ].join('\n');
  writeFile(path.join(base, 'copilot-instructions.md'), idx);

  // Per-skill: .github/skills/<name>/SKILL.md (+ references/, examples/)
  for (const skill of skills) {
    const s = loadSkill(agentSrc, skill);
    if (!s) continue;
    const out = fmYaml({ name: s.fm.name || s.name, description: s.fm.description || '' }) + s.body;
    writeFile(path.join(base, 'skills', s.name, 'SKILL.md'), out);
    for (const a of s.aux) {
      writeFile(path.join(base, 'skills', s.name, a.relPath), a.content);
    }
  }

  // Per-role: also emitted as skills (cloud-agent spec has no separate "agent" concept)
  for (const role of roles) {
    const a = loadAgent(agentSrc, role);
    if (!a) continue;
    const skillName = `agent-${a.name}`;
    const out = fmYaml({ name: skillName, description: a.fm.description || '' }) + a.body;
    writeFile(path.join(base, 'skills', skillName, 'SKILL.md'), out);
  }

  // Per-workflow prompt files (invoked manually via /command)
  for (const wf of ALL_WORKFLOWS) {
    const w = loadWorkflow(agentSrc, wf);
    if (!w) continue;
    const out = fmYaml({ mode: 'agent', description: w.fm.description || '' }) + w.body;
    writeFile(path.join(base, 'prompts', `${w.name}.prompt.md`), out);
  }
  return { dir: '.github/', skills: skills.length };
}

// ---- Gemini CLI: GEMINI.md + .gemini/{skills,agents,workflows}/ ----
function installGemini(agentSrc, targetDir, roles, skills) {
  const base = path.join(targetDir, '.gemini');
  const idx = [
    '# VLSI Kit — Gemini routing',
    '',
    'This project uses the VLSI Agent Kit.',
    'Skills, agents, and workflows live under `.gemini/`.',
    '',
    '## Skills',
    '',
    ...skills.map((s) => `- @.gemini/skills/${s}.md`),
    '',
    '## Agents (roles)',
    '',
    ...roles.map((r) => `- @.gemini/agents/${r}.md`),
    '',
    '## Workflows',
    '',
    ...ALL_WORKFLOWS.map((w) => `- /${w} → @.gemini/workflows/${w}.md`),
    '',
  ].join('\n');
  writeFile(path.join(targetDir, 'GEMINI.md'), idx);

  for (const skill of skills) {
    const s = loadSkill(agentSrc, skill);
    if (!s) continue;
    const out = fmYaml({ name: s.fm.name || s.name, description: s.fm.description || '' }) + s.body;
    writeFile(path.join(base, 'skills', `${s.name}.md`), out);
  }
  for (const role of roles) {
    const a = loadAgent(agentSrc, role);
    if (!a) continue;
    const out = fmYaml({ name: a.fm.name || a.name, description: a.fm.description || '' }) + a.body;
    writeFile(path.join(base, 'agents', `${a.name}.md`), out);
  }
  for (const wf of ALL_WORKFLOWS) {
    const w = loadWorkflow(agentSrc, wf);
    if (!w) continue;
    const out = fmYaml({ description: w.fm.description || '' }) + w.body;
    writeFile(path.join(base, 'workflows', `${w.name}.md`), out);
  }
  return { dir: '.gemini/ + GEMINI.md', skills: skills.length };
}

// ---- Cursor: .cursor/rules/*.mdc ----
function installCursor(agentSrc, targetDir, roles, skills) {
  const base = path.join(targetDir, '.cursor', 'rules');
  for (const skill of skills) {
    const s = loadSkill(agentSrc, skill);
    if (!s) continue;
    const out = fmYaml({ description: s.fm.description || '', alwaysApply: false }) + s.body;
    writeFile(path.join(base, `${s.name}.mdc`), out);
  }
  for (const role of roles) {
    const a = loadAgent(agentSrc, role);
    if (!a) continue;
    const out = fmYaml({ description: a.fm.description || '', alwaysApply: false }) + a.body;
    writeFile(path.join(base, `agent-${a.name}.mdc`), out);
  }
  for (const wf of ALL_WORKFLOWS) {
    const w = loadWorkflow(agentSrc, wf);
    if (!w) continue;
    const out = fmYaml({ description: w.fm.description || '', alwaysApply: false }) + w.body;
    writeFile(path.join(base, `workflow-${w.name}.mdc`), out);
  }
  return { dir: '.cursor/rules/', skills: skills.length };
}

// ---- Antigravity: AGENTS.md + .agents/{skills,workflows}/ ----
function installAntigravity(agentSrc, targetDir, roles, skills) {
  const base = path.join(targetDir, '.agents');
  const idx = [
    '# VLSI Kit — Agent routing',
    '',
    'This project follows the AGENTS.md convention.',
    'Skills, role agents, and workflows live under `.agents/`.',
    '',
    '## Skills',
    '',
    ...skills.map((s) => `- \`.agents/skills/${s}.md\``),
    '',
    '## Roles',
    '',
    ...roles.map((r) => `- \`.agents/roles/${r}.md\``),
    '',
    '## Workflows',
    '',
    ...ALL_WORKFLOWS.map((w) => `- \`.agents/workflows/${w}.md\``),
    '',
  ].join('\n');
  writeFile(path.join(targetDir, 'AGENTS.md'), idx);

  for (const skill of skills) {
    const s = loadSkill(agentSrc, skill);
    if (!s) continue;
    const out = fmYaml({ name: s.fm.name || s.name, description: s.fm.description || '' }) + s.body;
    writeFile(path.join(base, 'skills', `${s.name}.md`), out);
  }
  for (const role of roles) {
    const a = loadAgent(agentSrc, role);
    if (!a) continue;
    const out = fmYaml({ name: a.fm.name || a.name, description: a.fm.description || '' }) + a.body;
    writeFile(path.join(base, 'roles', `${a.name}.md`), out);
  }
  for (const wf of ALL_WORKFLOWS) {
    const w = loadWorkflow(agentSrc, wf);
    if (!w) continue;
    const out = fmYaml({ description: w.fm.description || '' }) + w.body;
    writeFile(path.join(base, 'workflows', `${w.name}.md`), out);
  }
  return { dir: 'AGENTS.md + .agents/', skills: skills.length };
}

const TOOL_INSTALLERS = {
  claude: installClaude,
  copilot: installCopilot,
  gemini: installGemini,
  cursor: installCursor,
  antigravity: installAntigravity,
};

async function init(targetDir = '.') {
  const packageDir = path.dirname(__dirname);
  const agentSrc = path.join(packageDir, '.agent');

  const yes = args.includes('-y') || args.includes('--yes');
  const toolsFlag = parseFlagValue('--tools');     // e.g. --tools=claude,copilot
  const rolesFlag = parseFlagValue('--roles');     // e.g. --roles=rtl-designer,verification-engineer
  const skillsFlag = parseFlagValue('--skills');   // e.g. --skills=fsm-design,uvm-coding or 'all'

  const ROLES = readRoles();
  const ALL_ROLES = Object.keys(ROLES).sort();

  log('\n🚀 VLSI Kit - AI Agent Kit for VLSI Development\n', COLORS.cyan + COLORS.bold);

  // Per-tool dirs are checked at install time, not here.
  // `.agent/` is no longer written to the user's project — bundled `.agent/`
  // inside the npm package keeps `vlsi-agkit` CLI working as a fallback.

  // ---------- Step 1: tool selection (none selected by default) ----------
  // `--yes` alone (no other flags) → install all tools.
  // `--yes` with `--roles=...` or `--skills=...` → no tools unless `--tools=...` given.
  const explicitlyScoped = !!rolesFlag || !!skillsFlag;
  let selectedTools;
  if (toolsFlag) {
    selectedTools = toolsFlag === 'all'
      ? Object.keys(TOOL_CONFIGS)
      : toolsFlag.split(',').map((t) => t.trim()).filter((t) => TOOL_CONFIGS[t]);
  } else if (yes && !explicitlyScoped) {
    selectedTools = Object.keys(TOOL_CONFIGS);
  } else if (yes) {
    selectedTools = [];   // user is being specific — don't auto-install tools
  } else {
    const toolChoices = Object.entries(TOOL_CONFIGS).map(([key, cfg]) => ({
      title: cfg.label,
      description: cfg.description,
      value: key,
      selected: false,   // nothing pre-selected — user opts in
    }));

    const result = await prompts({
      type: 'multiselect',
      name: 'tools',
      message: 'Which AI tools will you use? (none selected)',
      choices: toolChoices,
      hint: '- Space to select. Enter to confirm. (a) toggle all. Skip to install no tool config.',
      instructions: false,
    }, { onCancel: () => process.exit(1) });

    selectedTools = result.tools || [];
  }

  // ---------- Step 2: role selection → skills derived from roles ----------
  let selectedRoles;
  let selectedSkills;

  if (skillsFlag) {
    // Direct skill selection (advanced)
    selectedRoles = ALL_ROLES;  // include all role .md files even when picking skills directly
    selectedSkills = skillsFlag === 'all'
      ? ALL_SKILLS
      : skillsFlag.split(',').map((s) => s.trim()).filter((s) => ALL_SKILLS.includes(s));
  } else if (rolesFlag) {
    selectedRoles = rolesFlag === 'all'
      ? ALL_ROLES
      : rolesFlag.split(',').map((r) => r.trim()).filter((r) => ROLES[r]);
    selectedSkills = unionSkills(selectedRoles, ROLES);
  } else if (yes) {
    selectedRoles = ALL_ROLES;
    selectedSkills = ALL_SKILLS;
  } else {
    const roleChoices = ALL_ROLES.map((r) => ({
      title: r,
      description: shortDesc(ROLES[r].description),
      value: r,
      selected: false,   // nothing pre-selected
    }));

    const result = await prompts({
      type: 'multiselect',
      name: 'roles',
      message: 'Which roles do you need? (skills come bundled per role)',
      choices: roleChoices,
      hint: '- Space to select. Enter to confirm. (a) toggle all',
      instructions: false,
    }, { onCancel: () => process.exit(1) });

    selectedRoles = result.roles || [];
    if (selectedRoles.length === 0) {
      log('\nNo roles selected — installing all 14 roles + all 18 skills.\n', COLORS.yellow);
      selectedRoles = ALL_ROLES;
      selectedSkills = ALL_SKILLS;
    } else {
      selectedSkills = unionSkills(selectedRoles, ROLES);
      log(`\n→ Selected ${selectedRoles.length} role(s), bundling ${selectedSkills.length} skill(s):`, COLORS.cyan);
      log(`  ${selectedSkills.join(', ')}\n`, COLORS.gray);
    }
  }

  // ---------- Step 3: install per tool ----------
  if (selectedTools.length === 0) {
    log('\n⚠️  No tools selected. Nothing to write.', COLORS.yellow);
    log('   The kit is still usable via the `vlsi-agkit` CLI (reads from npm bundle).', COLORS.gray);
    log('\n📖 Try:', COLORS.cyan);
    log('   vlsi-agkit list            # browse skills, agents, workflows');
    log('   vlsi-agkit skill <name>    # read a skill from terminal');
    log('   vlsi-agkit search <query>  # search the kit\n');
    return;
  }

  log(`\n${COLORS.bold}Installing...${COLORS.reset}`, COLORS.cyan);
  const summaries = [];
  for (const tool of selectedTools) {
    const installer = TOOL_INSTALLERS[tool];
    if (!installer) continue;
    const cfg = TOOL_CONFIGS[tool];
    const dir = path.join(targetDir, cfg.label.split(' ')[0].toLowerCase()); // not used; just log below
    log(`📦 ${cfg.label} → ${cfg.description}`);
    const result = installer(agentSrc, targetDir, selectedRoles, selectedSkills);
    summaries.push({ tool, label: cfg.label, ...result });
  }

  // ---------- Done ----------
  log(`\n✅ VLSI Kit initialized!\n`, COLORS.green + COLORS.bold);
  log('📦 Installed:', COLORS.cyan);
  log(`   • ${selectedRoles.length} role(s): ${selectedRoles.join(', ')}`);
  log(`   • ${selectedSkills.length} skill(s) per tool`);
  log(`   • ${ALL_WORKFLOWS.length} workflows per tool`);
  log('\n📄 Tool configs written:', COLORS.cyan);
  summaries.forEach((s) => log(`   ✓ ${s.label.padEnd(20)} ${COLORS.gray}${s.dir}${COLORS.reset}`));
  log('\n📖 Try the CLI too (works from any directory):', COLORS.cyan);
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
  log('  init                        Interactive install (prompts for tools + roles)');
  log('  init --yes                  Non-interactive: install ALL tools, roles, and skills');
  log('  init --tools=<list>         Comma-list of tools (claude,copilot,gemini,cursor,antigravity,all)');
  log('  init --roles=<list>         Comma-list of role names or "all" (skills derived from roles)');
  log('  init --skills=<list>        Direct skill selection (advanced; bypasses role mapping)');
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
