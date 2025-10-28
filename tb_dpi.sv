module tb_dpi;

// simulation clock period
localparam PERIOD = 1;
initial forever #PERIOD clk = !clk;

// master clk and master rst_n
bit clk, sysrst_n,rst_n, ndmreset;
assign rst_n = !ndmreset & sysrst_n;
// Debugging
bit tdo, tdo_en, tclk, tdi, tms, trst, tclk_en, tclk_gen;

logic [33+7:0] drscan = 0;
logic [7:0] gpio;
logic enable_jtag_dpi;

jtag_dpi_remote_bit_bang #(
  .TCP_PORT(4567)
) jtag_dpi  (     
    .clk_i(clk),
    .enable_i(enable_jtag_dpi),
    .jtag_tms_o(tms),
    .jtag_tck_o(tclk),
    .jtag_trst_o(),
    .jtag_srst_o(),
    .jtag_tdi_o(tdi),
    .jtag_tdo_i(tdo),
    .blink_o()
);

soc soc(.*); // The SoC

initial begin
    enable_jtag_dpi = 0;
    sysrst_n = 1;

    // reset
    #1;
    sysrst_n = 0;
    # 1;
    sysrst_n = 1;

    trst = 1;
    #1 trst = 0;
    #1 trst = 1;

    #10;
    enable_jtag_dpi = 1;
end

initial begin
    // dump everything
    $dumpfile("dumpfile.fst");
    $dumpvars(0, top);

    // initialize ROM memory
    $readmemh("rom.mi", soc.rom0.wrapped_mem.mem,0,250);

    // initialize RAM memory
    //$readmemh("memory.hex", mem0.wrapped_mem.mem,0,1000);
    // word addressed
    soc.mem0.wrapped_mem.mem[0] = 32'hDEAD0000; 
    soc.mem0.wrapped_mem.mem[1] = 32'hDEAD0001; 
    soc.mem0.wrapped_mem.mem[2] = 32'hDEAD0002; 
    soc.mem0.wrapped_mem.mem[3] = 32'hDEAD0003; 
    soc.mem0.wrapped_mem.mem[4] = 32'hDEAD0004; 
    soc.mem0.wrapped_mem.mem[5] = 32'hDEAD0005; 
    soc.mem0.wrapped_mem.mem[6] = 32'hDEAD0006; 
    soc.mem0.wrapped_mem.mem[7] = 32'hDEAD0007; 
    soc.mem0.wrapped_mem.mem[8] = 32'hDEAD0008; 
    soc.mem0.wrapped_mem.mem[9] = 32'hDEAD0009; 
    soc.mem0.wrapped_mem.mem[10] = 32'hDEAD0010; 
end

endmodule