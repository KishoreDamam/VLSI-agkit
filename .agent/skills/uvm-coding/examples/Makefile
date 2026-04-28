# UVM examples require a UVM library -- cannot compile with iverilog
# Run with: make verify TOOL=questa  (or vcs, xcelium)
tier := needs-vendor-sim

REPO_ROOT ?= $(abspath $(CURDIR)/../../../../..)

include $(REPO_ROOT)/tools.mk

.PHONY: verify clean

verify: $(SIM_VERIFY_TARGET)

clean:
	$(SIM_CLEAN)
