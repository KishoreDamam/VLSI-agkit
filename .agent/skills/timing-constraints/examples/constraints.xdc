# constraints.xdc — Example timing constraints for a small FPGA design
#
# Design: a hypothetical SoC with two clock domains, an APB bus,
# a DDR-like data interface, and a slow configuration register path.
#
# Target: Xilinx Ultrascale+ (e.g., XCZU7EV)
# Standard: SDC 1.9 with XDC extensions
#
# ─────────────────────────────────────────────────────────────────────────────
# SECTION 1: Primary clock declarations
# ─────────────────────────────────────────────────────────────────────────────
# Each independent board-level clock source gets one create_clock.
# Period is in nanoseconds; 200 MHz → 5.000 ns, 50 MHz → 20.000 ns.

create_clock -name clk_sys -period 5.000 [get_ports clk_sys_p]
#   clk_sys: 200 MHz system clock (differential LVDS input, P-side only)

create_clock -name clk_apb -period 20.000 [get_ports clk_apb]
#   clk_apb: 50 MHz APB peripheral clock (single-ended)

# ─────────────────────────────────────────────────────────────────────────────
# SECTION 2: Xilinx I/O pin and standard assignments
# ─────────────────────────────────────────────────────────────────────────────
# Every board-connected port must have PACKAGE_PIN and IOSTANDARD set.
# Pin numbers are for illustration — substitute from your board schematic.

set_property PACKAGE_PIN AK17    [get_ports clk_sys_p]
set_property IOSTANDARD  LVDS    [get_ports clk_sys_p]

set_property PACKAGE_PIN W5      [get_ports clk_apb]
set_property IOSTANDARD  LVCMOS33 [get_ports clk_apb]

set_property PACKAGE_PIN AB12    [get_ports rst_n]
set_property IOSTANDARD  LVCMOS33 [get_ports rst_n]

# ─────────────────────────────────────────────────────────────────────────────
# SECTION 3: Clock groups — declare asynchronous relationships
# ─────────────────────────────────────────────────────────────────────────────
# clk_sys and clk_apb come from independent oscillators on the board and
# share no timing relationship. Declaring them asynchronous tells STA not
# to analyze paths between them — those crossings must use synchronizers.
#
# Note: this does NOT replace synchronizers; all signals that actually cross
# between clk_sys and clk_apb domains must be synchronized in RTL.

set_clock_groups -asynchronous \
    -group [get_clocks clk_sys] \
    -group [get_clocks clk_apb]

# ─────────────────────────────────────────────────────────────────────────────
# SECTION 4: I/O delays — system-synchronous inputs and outputs
# ─────────────────────────────────────────────────────────────────────────────
# Budget derivation (system-synchronous, 200 MHz, shared board clock):
#   -max = t_co_max + t_trace  = 1.5 + 0.5 = 2.0 ns  (setup analysis)
#   -min = t_co_min - t_trace  = 1.0 - 0.5 = 0.5 ns  (hold analysis)
#
# Both -max and -min must be specified; omitting -min leaves hold
# at the I/O boundary unconstrained.

set_input_delay -clock clk_sys -max 2.0 [get_ports data_in*]
set_input_delay -clock clk_sys -min 0.5 [get_ports data_in*]

# Output delay to a downstream device:
#   -max = t_su_receiver + t_trace = 2.0 + 0.5 = 2.5 ns
#   -min = t_hold_receiver - t_trace = 0.0 - 0.5 = -0.5 ns
# Negative -min is valid: data leaves FPGA pin earlier than the reference edge.

set_output_delay -clock clk_sys -max 2.5 [get_ports data_out*]
set_output_delay -clock clk_sys -min -0.5 [get_ports data_out*]

# APB register bus I/O (slower clock, larger budget)
set_input_delay  -clock clk_apb -max 5.0 [get_ports apb_prdata*]
set_input_delay  -clock clk_apb -min 1.0 [get_ports apb_prdata*]
set_output_delay -clock clk_apb -max 6.0 [get_ports apb_pwdata*]
set_output_delay -clock clk_apb -min -1.0 [get_ports apb_pwdata*]

# ─────────────────────────────────────────────────────────────────────────────
# SECTION 5: False path — asynchronous reset
# ─────────────────────────────────────────────────────────────────────────────
# rst_n is an asynchronous reset asserted by board logic with no timing
# relationship to clk_sys. STA cannot meaningfully analyze the assertion
# edge; false-path it to suppress spurious violations.
#
# Deassertion is handled by per-domain reset synchronizers in RTL —
# the synchronized reset signal is constrained by normal setup/hold analysis.

set_false_path -from [get_ports rst_n]

# ─────────────────────────────────────────────────────────────────────────────
# SECTION 6: Multicycle path — slow data path (N=2)
# ─────────────────────────────────────────────────────────────────────────────
# The divider result register (div_result_reg) is captured every 2 clock
# cycles — the divider is a 2-cycle iterative unit, and the enable on
# div_result_reg fires only on even cycles.
#
# set_multicycle_path 2 -setup: allows 2 × 5 ns = 10 ns for the path.
# set_multicycle_path 1 -hold:  compensates the hold check; without this,
#   the hold window shifts to cycle +1, potentially missing a real violation
#   from data launched at cycle +1 overwriting the intended cycle +0 launch.

set_multicycle_path 2 -setup \
    -from [get_cells u_divider/div_stage_reg*/Q] \
    -to   [get_cells u_divider/div_result_reg*/D]

set_multicycle_path 1 -hold \
    -from [get_cells u_divider/div_stage_reg*/Q] \
    -to   [get_cells u_divider/div_result_reg*/D]

# ─────────────────────────────────────────────────────────────────────────────
# SECTION 7: CDC max-delay — gray-coded pointer for async FIFO
# ─────────────────────────────────────────────────────────────────────────────
# The async FIFO gray-pointer crosses from clk_apb (50 MHz, 20 ns period)
# to clk_sys (200 MHz, 5 ns period). The pointer must arrive within one
# destination clock period so the 2-FF synchronizer in the read domain
# can sample it correctly.
#
# Use set_max_delay -datapath_only (NOT set_false_path): the -datapath_only
# flag bounds the routing delay without removing clock skew analysis.
# Value = destination clock period = 5.0 ns.

set_max_delay 5.0 -datapath_only \
    -from [get_cells u_async_fifo/wr_ptr_gray_reg*/Q] \
    -to   [get_cells u_async_fifo/rd_sync_reg*[0]/D]
