###########################################################
# constraints.sdc -- companion SDC for the STA example.
#
# This file is not used by `make verify` (which only compiles
# the SV and runs the TB). It exists as a *reference* that
# pairs with the worked-example numbers in
# references/setup-hold-equations.md.
#
# To use with PrimeTime / Vivado / Tempus, load the netlist
# elaborated from pipelined_alu.sv and source this script.
###########################################################

# 1 GHz primary clock
create_clock -name clk -period 1.000 [get_ports clk]

# Pre-CTS uncertainty budget (jitter + est. skew + margin)
set_clock_uncertainty -setup 0.080 [get_clocks clk]
set_clock_uncertainty -hold  0.030 [get_clocks clk]

# Conservative flat OCV for the example. At 28nm+, replace with
# AOCV; at 16nm+, with POCV. See references/ocv-aocv-pocv.md.
set_timing_derate -late  1.05 -cell_delay
set_timing_derate -early 0.95 -cell_delay
set_timing_derate -late  1.05 -net_delay
set_timing_derate -early 0.95 -net_delay

# I/O budget -- generous since this is for the STA reading exercise
set_input_delay  -clock clk -max 0.200 [get_ports {a[*] b[*] c[*] op[*]}]
set_input_delay  -clock clk -min 0.050 [get_ports {a[*] b[*] c[*] op[*]}]
set_output_delay -clock clk -max 0.150 [get_ports {y[*]}]
set_output_delay -clock clk -min 0.050 [get_ports {y[*]}]

# False path on the async reset deassertion -- a typical pattern.
# Recovery/removal will still be checked unless you add the line
# below; see references/timing-paths.md.
set_false_path -from [get_ports rst_n]
