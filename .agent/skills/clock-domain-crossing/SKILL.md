---
name: clock-domain-crossing
description: CDC techniques, synchronizers, and safe data transfer.
---

# Clock Domain Crossing

> Techniques for safe data transfer between clock domains.

---

## CDC Types

| Type | Signal | Solution |
|------|--------|----------|
| Single bit | Control | 2-FF synchronizer |
| Multi-bit | Counter/pointer | Gray code |
| Bus | Data | FIFO |
| Pulse | Strobe | Pulse sync |

---

## 2-FF Synchronizer

```systemverilog
module sync_2ff #(
    parameter int WIDTH = 1,
    parameter int STAGES = 2
) (
    input  logic             clk_dst,
    input  logic             rst_n,
    input  logic [WIDTH-1:0] async_in,
    output logic [WIDTH-1:0] sync_out
);

    (* ASYNC_REG = "TRUE" *)
    logic [WIDTH-1:0] sync_reg [STAGES];
    
    always_ff @(posedge clk_dst or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < STAGES; i++)
                sync_reg[i] <= '0;
        end else begin
            sync_reg[0] <= async_in;
            for (int i = 1; i < STAGES; i++)
                sync_reg[i] <= sync_reg[i-1];
        end
    end
    
    assign sync_out = sync_reg[STAGES-1];

endmodule
```

---

## Pulse Synchronizer

```systemverilog
module pulse_sync (
    input  logic clk_src,
    input  logic clk_dst,
    input  logic rst_n,
    input  logic pulse_in,
    output logic pulse_out
);

    logic toggle_src;
    logic toggle_dst, toggle_dst_d;
    
    // Toggle on pulse in source domain
    always_ff @(posedge clk_src or negedge rst_n) begin
        if (!rst_n)
            toggle_src <= 1'b0;
        else if (pulse_in)
            toggle_src <= ~toggle_src;
    end
    
    // Sync toggle to destination
    sync_2ff u_sync (
        .clk_dst  (clk_dst),
        .rst_n    (rst_n),
        .async_in (toggle_src),
        .sync_out (toggle_dst)
    );
    
    // Detect edge in destination
    always_ff @(posedge clk_dst or negedge rst_n) begin
        if (!rst_n)
            toggle_dst_d <= 1'b0;
        else
            toggle_dst_d <= toggle_dst;
    end
    
    assign pulse_out = toggle_dst ^ toggle_dst_d;

endmodule
```

---

## Gray Code

```systemverilog
// Binary to Gray
function automatic logic [WIDTH-1:0] bin2gray(
    input logic [WIDTH-1:0] bin
);
    return bin ^ (bin >> 1);
endfunction

// Gray to Binary
function automatic logic [WIDTH-1:0] gray2bin(
    input logic [WIDTH-1:0] gray
);
    logic [WIDTH-1:0] bin;
    bin[WIDTH-1] = gray[WIDTH-1];
    for (int i = WIDTH-2; i >= 0; i--)
        bin[i] = bin[i+1] ^ gray[i];
    return bin;
endfunction
```

---

## Async FIFO

```systemverilog
module async_fifo #(
    parameter int WIDTH = 8,
    parameter int DEPTH = 16
) (
    // Write side
    input  logic             wr_clk,
    input  logic             wr_rst_n,
    input  logic [WIDTH-1:0] wr_data,
    input  logic             wr_en,
    output logic             wr_full,
    
    // Read side
    input  logic             rd_clk,
    input  logic             rd_rst_n,
    output logic [WIDTH-1:0] rd_data,
    input  logic             rd_en,
    output logic             rd_empty
);

    localparam ADDR_WIDTH = $clog2(DEPTH);
    
    // Memory
    logic [WIDTH-1:0] mem [DEPTH];
    
    // Pointers (binary and gray)
    logic [ADDR_WIDTH:0] wr_ptr, wr_ptr_gray;
    logic [ADDR_WIDTH:0] rd_ptr, rd_ptr_gray;
    
    // Synchronized pointers
    logic [ADDR_WIDTH:0] wr_ptr_gray_sync;
    logic [ADDR_WIDTH:0] rd_ptr_gray_sync;
    
    // Write logic
    always_ff @(posedge wr_clk or negedge wr_rst_n) begin
        if (!wr_rst_n) begin
            wr_ptr <= '0;
        end else if (wr_en && !wr_full) begin
            mem[wr_ptr[ADDR_WIDTH-1:0]] <= wr_data;
            wr_ptr <= wr_ptr + 1;
        end
    end
    
    assign wr_ptr_gray = bin2gray(wr_ptr);
    
    // Read logic
    always_ff @(posedge rd_clk or negedge rd_rst_n) begin
        if (!rd_rst_n)
            rd_ptr <= '0;
        else if (rd_en && !rd_empty)
            rd_ptr <= rd_ptr + 1;
    end
    
    assign rd_data = mem[rd_ptr[ADDR_WIDTH-1:0]];
    assign rd_ptr_gray = bin2gray(rd_ptr);
    
    // Sync write pointer to read domain
    sync_2ff #(.WIDTH(ADDR_WIDTH+1)) u_sync_wr (
        .clk_dst  (rd_clk),
        .rst_n    (rd_rst_n),
        .async_in (wr_ptr_gray),
        .sync_out (wr_ptr_gray_sync)
    );
    
    // Sync read pointer to write domain
    sync_2ff #(.WIDTH(ADDR_WIDTH+1)) u_sync_rd (
        .clk_dst  (wr_clk),
        .rst_n    (wr_rst_n),
        .async_in (rd_ptr_gray),
        .sync_out (rd_ptr_gray_sync)
    );
    
    // Full/Empty
    assign rd_empty = (rd_ptr_gray == wr_ptr_gray_sync);
    assign wr_full = (wr_ptr_gray == {~rd_ptr_gray_sync[ADDR_WIDTH:ADDR_WIDTH-1],
                                       rd_ptr_gray_sync[ADDR_WIDTH-2:0]});

endmodule
```

---

## Handshake Protocol

```systemverilog
module handshake_sync #(
    parameter int WIDTH = 32
) (
    // Source domain
    input  logic             src_clk,
    input  logic             src_rst_n,
    input  logic [WIDTH-1:0] src_data,
    input  logic             src_valid,
    output logic             src_ready,
    
    // Destination domain
    input  logic             dst_clk,
    input  logic             dst_rst_n,
    output logic [WIDTH-1:0] dst_data,
    output logic             dst_valid,
    input  logic             dst_ready
);
    // REQ-ACK handshake with data hold
endmodule
```

---

## CDC Constraints

```tcl
# Set max delay for synchronizer
set_max_delay -from [get_cells src_reg] \
    -to [get_cells sync_reg[0]] \
    -datapath_only $period

# Or false path (less coverage)
set_false_path -from [get_clocks src_clk] \
    -to [get_clocks dst_clk]
```

---

## Best Practices

| Practice | Reason |
|----------|--------|
| Use 2+ FF stages | Reduce MTBF |
| Gray code for counters | Single bit change |
| ASYNC_REG attribute | Tool optimization |
| Hold data stable | Prevent glitches |
| Review CDC reports | Catch violations |
