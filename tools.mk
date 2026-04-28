# tools.mk — simulator discovery and rule selection
#
# Included by every <skill>/examples/Makefile. Picks a simulator using:
#   1. PATH lookup
#   2. VLSI_SIM env var (overrides PATH choice)
#   3. .agent/tools.local.mk (optional, gitignored)
#
# Defines, for use by includer:
#   $(SIM_VERIFY_TARGET) — the make target that performs the tier's verify
#   $(SIM_CLEAN)         — shell snippet that removes simulator artifacts
#
# Required from includer (before including this file):
#   REPO_ROOT — absolute path to the repo root (set by includer; we DO NOT
#                guess via $(MAKEFILE_LIST) because that's fragile across
#                recursive invocations and includer locations).
#   tier      — one of: build-sim, build-only, tool-output, needs-vendor-sim,
#                manual-review (hyphenated to avoid Make whitespace foot-guns).
#   SRCS      — list of source files
#   TOP       — top-level module (testbench for build-sim, DUT for build-only)

SHELL := /bin/sh

ifndef REPO_ROOT
$(error tools.mk: REPO_ROOT must be set by includer (typically the skill's examples/Makefile))
endif

# 1. Optional per-user override (silent if absent). Anchored to REPO_ROOT —
#    no MAKEFILE_LIST guessing.
-include $(REPO_ROOT)/.agent/tools.local.mk

# 2. Validate tier early so authoring typos fail loud, before any
#    environmental check (simulator discovery) can mask them.
VALID_TIERS := build-sim build-only tool-output needs-vendor-sim manual-review
ifeq ($(filter $(tier),$(VALID_TIERS)),)
$(error tools.mk: tier='$(tier)' is not one of: $(VALID_TIERS). Check for trailing whitespace in your Makefile's `tier := ...` line.)
endif

# 3. Resolve simulator: env var wins, else first one found on PATH.
#    Note: command -v works in both bash and dash; SHELL := /bin/sh forces
#    a POSIX shell so this is portable across Linux/macOS/Git-Bash.
ifndef VLSI_SIM
  ifneq (,$(shell command -v iverilog 2>/dev/null))
    VLSI_SIM := iverilog
  else ifneq (,$(shell command -v xsim 2>/dev/null))
    VLSI_SIM := xsim
  else ifneq (,$(shell command -v vcs 2>/dev/null))
    VLSI_SIM := vcs
  else ifneq (,$(shell command -v xrun 2>/dev/null))
    VLSI_SIM := xrun
  else ifneq (,$(shell command -v vsim 2>/dev/null))
    VLSI_SIM := vsim
  endif
endif

# 4. Apply VLSI_SIM_BIN if user provided it
ifdef VLSI_SIM_BIN
  SIM_PREFIX := $(VLSI_SIM_BIN)/
else
  SIM_PREFIX :=
endif

# 5. Bail out clearly if nothing is found
ifndef VLSI_SIM
$(error No SystemVerilog simulator found on PATH. Expected one of: xsim, iverilog, vcs, xrun, vsim. Either add the simulator to PATH (typical: `source <vendor>/settings64.sh`) or set VLSI_SIM in .agent/tools.local.mk (see tools.example.mk))
endif

# 6. Tier-aware skips (do NOT depend on simulator)
ifeq ($(tier),tool-output)
SIM_VERIFY_TARGET := tool-output-skip
SIM_CLEAN         := :
tool-output-skip:
	@echo "tool-output: no automated check — review constraints manually"
endif

ifeq ($(tier),manual-review)
SIM_VERIFY_TARGET := manual-review-skip
SIM_CLEAN         := :
manual-review-skip:
	@echo "[SKIP] tier=manual-review for $(CURDIR) — see SKILL.md for review notes"
endif

ifeq ($(tier),needs-vendor-sim)
  ifeq ($(VLSI_SIM),iverilog)
# iverilog can't run vendor-only constructs — skip with a clear message
SIM_VERIFY_TARGET := needs-vendor-sim-skip
SIM_CLEAN         := :
needs-vendor-sim-skip:
	@echo "[SKIP] tier=needs-vendor-sim, VLSI_SIM=iverilog for $(CURDIR) — manual diff required against expected log"
  else
# Vendor simulator available — alias needs-vendor-sim to build-sim so the
# per-simulator rules below run the actual verify.
override tier := build-sim
  endif
endif

# 7. Per-simulator rules (only set if SIM_VERIFY_TARGET still empty —
#    skip-paths above take priority)
ifndef SIM_VERIFY_TARGET
ifeq ($(VLSI_SIM),iverilog)
  IVERILOG_FLAGS := -g2012 -Wall

  ifeq ($(tier),build-sim)
SIM_VERIFY_TARGET := iverilog-build-sim
SIM_CLEAN         := rm -f a.out *.vvp

iverilog-build-sim:
	$(SIM_PREFIX)iverilog $(IVERILOG_FLAGS) -s $(TOP) -o a.out $(SRCS)
	$(SIM_PREFIX)vvp a.out
  endif

  ifeq ($(tier),build-only)
SIM_VERIFY_TARGET := iverilog-build-only
SIM_CLEAN         := rm -f a.out

iverilog-build-only:
	$(SIM_PREFIX)iverilog $(IVERILOG_FLAGS) -tnull -s $(TOP) $(SRCS)
  endif
endif

ifeq ($(VLSI_SIM),xsim)
  XVLOG_FLAGS := --sv

  ifeq ($(tier),build-sim)
SIM_VERIFY_TARGET := xsim-build-sim
SIM_CLEAN         := rm -rf xsim.dir *.jou *.pb *.log

xsim-build-sim:
	$(SIM_PREFIX)xvlog $(XVLOG_FLAGS) $(SRCS)
	$(SIM_PREFIX)xelab -debug typical $(TOP) -s $(TOP)_snapshot
	$(SIM_PREFIX)xsim $(TOP)_snapshot -R
  endif

  ifeq ($(tier),build-only)
SIM_VERIFY_TARGET := xsim-build-only
SIM_CLEAN         := rm -rf xsim.dir *.jou *.pb *.log

xsim-build-only:
	$(SIM_PREFIX)xvlog $(XVLOG_FLAGS) $(SRCS)
	$(SIM_PREFIX)xelab $(TOP)
  endif
endif
endif # ifndef SIM_VERIFY_TARGET
