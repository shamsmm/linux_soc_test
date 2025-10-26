module tb_dpi;

// simulation clock period
localparam PERIOD = 50;
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
end

endmodule