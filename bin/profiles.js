const fs = require('node:fs');
const path = require('node:path');
const { readFrontmatter } = require('./fs-util');

const ALWAYS_INCLUDE = ['orchestrator', 'project-planner'];

const PROFILES = [
  {
    id: 'full-stack',
    name: 'Full Stack',
    description: 'All 14 VLSI specialist agents — the original behavior',
    agents: [
      'orchestrator', 'rtl-designer', 'verification-engineer',
      'synthesis-engineer', 'timing-analyst', 'fpga-specialist',
      'asic-specialist', 'physical-design-engineer', 'debugger',
      'lint-reviewer', 'documentation-writer', 'project-planner',
      'ip-integrator', 'power-analyst'
    ],
    workflows: [
      'brainstorm', 'plan', 'design', 'verify', 'synthesize',
      'debug', 'lint', 'timing', 'review', 'integrate'
    ],
    alwaysInclude: [],   // full-stack already has everything
    extraSkills: [],
    isFullStack: true
  },
  {
    id: 'fpga-engineer',
    name: 'FPGA Engineer',
    description: 'FPGA design, Vivado/Quartus flows, timing closure',
    agents: ['fpga-specialist', 'rtl-designer', 'timing-analyst',
             'ip-integrator', 'debugger', 'lint-reviewer'],
    workflows: ['design', 'debug', 'lint', 'timing', 'integrate'],
    alwaysInclude: ALWAYS_INCLUDE,
    extraSkills: []
  },
  {
    id: 'asic-engineer',
    name: 'ASIC Engineer',
    description: 'ASIC flows, DFT, tapeout',
    agents: ['asic-specialist', 'rtl-designer', 'physical-design-engineer',
             'timing-analyst', 'power-analyst', 'debugger', 'lint-reviewer'],
    workflows: ['design', 'synthesize', 'timing', 'lint', 'review'],
    alwaysInclude: ALWAYS_INCLUDE,
    extraSkills: []
  },
  {
    id: 'verification-engineer',
    name: 'Verification Engineer',
    description: 'UVM, formal, coverage',
    agents: ['verification-engineer', 'debugger', 'lint-reviewer',
             'documentation-writer'],
    workflows: ['verify', 'debug', 'review'],
    alwaysInclude: ALWAYS_INCLUDE,
    extraSkills: []
  },
  {
    id: 'rtl-designer',
    name: 'RTL Designer',
    description: 'Core RTL design focus',
    agents: ['rtl-designer', 'lint-reviewer', 'documentation-writer'],
    workflows: ['design', 'lint', 'review'],
    alwaysInclude: ALWAYS_INCLUDE,
    extraSkills: []
  },
  {
    id: 'physical-design',
    name: 'Physical Design',
    description: 'P&R, floorplanning, power',
    agents: ['physical-design-engineer', 'timing-analyst',
             'power-analyst', 'asic-specialist'],
    workflows: ['synthesize', 'timing', 'review'],
    alwaysInclude: ALWAYS_INCLUDE,
    extraSkills: []
  }
];

const BY_ID = Object.fromEntries(PROFILES.map(p => [p.id, p]));
const VALID_IDS = new Set(PROFILES.map(p => p.id));

function list() { return PROFILES.slice(); }

function _expandSkills(agentIds, agentsDir) {
  const skills = new Set();
  for (const id of agentIds) {
    const file = path.join(agentsDir, `${id}.md`);
    if (!fs.existsSync(file)) {
      console.warn(`[profiles] warning: agent file missing: ${file}`);
      continue;
    }
    const { data } = readFrontmatter(file);
    const decl = data.skills;
    if (!decl) continue;
    // `skills` is a comma-separated string in agent frontmatter;
    // split here (parser intentionally keeps it literal — see fs-util.js).
    const items = decl.split(',').map(s => s.trim()).filter(Boolean);
    for (const s of items) skills.add(s);
  }
  return [...skills];
}

function resolve(id, agentsDir) {
  const profile = BY_ID[id];
  if (!profile) {
    const valid = [...VALID_IDS].join(', ');
    throw new Error(`Unknown role profile "${id}". Valid ids: ${valid}`);
  }
  const agents = [...new Set([...profile.agents, ...profile.alwaysInclude])];
  const skills = [...new Set([
    ..._expandSkills(agents, agentsDir),
    ...profile.extraSkills
  ])];
  return {
    id: profile.id,
    name: profile.name,
    description: profile.description,
    agents,
    skills,
    workflows: profile.workflows.slice(),
    isFullStack: !!profile.isFullStack
  };
}

module.exports = { list, resolve, VALID_IDS, _expandSkills };
