// Agent -> Cursor/Windsurf glob map. Agents not in the map default to alwaysApply.
const GLOBS = {
  'rtl-designer':       ['**/*.{sv,svh,v,vh,vhd,vhdl}'],
  'ip-integrator':      ['**/*.{sv,svh,v,vh,vhd,vhdl}'],
  'verification-engineer': ['**/{tb,test,tests,sim}/**/*.{sv,svh,v}', '**/*_tb.{sv,v}'],
  'synthesis-engineer': ['**/*.{tcl,sdc}', '**/synth/**'],
  'timing-analyst':     ['**/*.{sdc,xdc,tcl}'],
  'fpga-specialist':    ['**/*.{xdc,qsf,xpr}', '**/fpga/**'],
  'asic-specialist':    ['**/*.{lef,def,lib,sdc}', '**/pnr/**', '**/synth/**'],
  'physical-design-engineer': ['**/*.{lef,def,lib,sdc}', '**/pnr/**', '**/synth/**'],
  'power-analyst':      ['**/*.upf', '**/power/**']
};

function globsFor(agentId) { return GLOBS[agentId] ?? null; }
function isAlwaysApply(agentId) { return !(agentId in GLOBS); }

function buildRuleFrontmatter(agentId, description) {
  const lines = ['---', `description: ${description}`];
  if (isAlwaysApply(agentId)) {
    lines.push('alwaysApply: true');
  } else {
    const g = globsFor(agentId);
    const v = g.length === 1 ? JSON.stringify(g[0]) : JSON.stringify(g.join(','));
    lines.push(`globs: ${v}`);
    lines.push('alwaysApply: false');
  }
  lines.push('---', '');
  return lines.join('\n');
}

module.exports = { globsFor, isAlwaysApply, buildRuleFrontmatter };
