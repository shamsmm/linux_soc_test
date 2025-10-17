module top;

// simulation clock period and timeout
localparam PERIOD = 5;
localparam JTAG_PERIOD = PERIOD * 18; // simulates 1MHz to 18MHz for example
localparam TIMEOUT = 50000;

// master clk and master rst_n
bit clk, sysrst_n,rst_n;
assign rst_n = !ndmreset & sysrst_n;
// Debugging
bit tdo, tdo_en, tclk, tdi, tms, trst, tclk_en, tclk_gen;
logic [31:0] drscan = 0;
always tclk = tclk_en ? tclk_gen : 0;
initial #0.3 forever #JTAG_PERIOD tclk_gen = ~tclk_gen;

// riscv32 core-0 master interfaces to I-bus and D-bus
master_bus_if dbus_if_core0(clk, rst_n);
master_bus_if ibus_if_core0(clk, rst_n);

// dual port memory interface to I-bus and D-bus 
slave_bus_if dbus_if_mem0(clk, rst_n);
slave_bus_if ibus_if_mem0(clk, rst_n);

// flash rom interface (read only) to bus (I-bus)
slave_bus_if ibus_if_rom0(clk, rst_n);

// gpio memory mapped interface to bus (D-bus)
slave_bus_if dbus_if_gpio0(clk, rst_n);

// plic (D-bus)
slave_bus_if dbus_if_plic0(clk, rst_n);

// clit (D-bus)
slave_bus_if dbus_if_clit0(clk, rst_n);

// riscv32 core-0
logic irq_sw0, irq_timer0, running, halted, haltreq, resumereq, resethaltreq;
rv_core #(.INITIAL_PC(32'h2000_0000)) core0(.haltreq(haltreq), .resumereq(resumereq), .resethaltreq(resethaltreq), .ibus(ibus_if_core0), .dbus(dbus_if_core0), .clk(clk), .rst_n(rst_n), .irq_sw(irq_sw0), .irq_timer(irq_timer0), .halted(halted), .running(running));

// dual port memory
memory_wrapped mem0(.ibus(ibus_if_mem0), .dbus(dbus_if_mem0), .clk(clk), .rst_n(rst_n));

// rom single port memory
rom_wrapped rom0(.bus(ibus_if_rom0), .clk(clk), .rst_n(rst_n));

// gpio memory mapped
gpio_wrapped gpio0(.bus(dbus_if_gpio0), .clk(clk));

// clint
clint clint0(.bus(dbus_if_clit0), .clk(clk), .irq_sw(irq_sw0), .irq_timer(irq_timer0), .rst_n(rst_n));

// interconnect

dbus_interconnect dbus_ic(.*);
ibus_interconnect ibus_ic(.*);

// Debug
// CDC synchronizes needed between JTAG and System clock

bit dmi_start_dtm;
logic [1:0] dmi_op_dtm;
logic [33:2] dmi_data_o_dtm, dmi_data_i_dtm;
logic [7+33:34] dmi_address_dtm;
logic dmi_finish_dtm;
dtm_jtag debug_transport(.tdi(tdi), .trst(trst), .tms(tms), .tclk(tclk), .tdo(tdo), .tdo_en(tdo_en), .dmi_start(dmi_start_dtm), .dmi_op(dmi_op_dtm), .dmi_data_o(dmi_data_o_dtm), .dmi_address(dmi_address_dtm), .dmi_finish(dmi_finish_dtm), .dmi_data_i(dmi_data_i_dtm));

logic ndmreset;
bit dmi_start_dm;
logic [1:0] dmi_op_dm;
logic [33:2] dmi_data_o_dm, dmi_data_i_dm;
logic [7+33:34] dmi_address_dm;
logic dmi_finish_dm;
dm debug_module(.haltreq(haltreq), .resumereq(resumereq), .resethaltreq(resethaltreq), .halted(halted), .running(running), .clk(clk), .rst_n(rst_n), .ndmreset(ndmreset), .dmi_start(dmi_start_dm), .dmi_op(dmi_op_dm), .dmi_data_o(dmi_data_o_dm), .dmi_address(dmi_address_dm), .dmi_finish(dmi_finish_dm), .dmi_data_i(dmi_data_i_dm));

// assertions and coverage
property dbus_access_valid;
    @(posedge clk)
    dbus_if_core0.bstart && !rst_n |-> |{dbus_if_mem0.ss, dbus_if_gpio0.ss};
endproperty

property ibus_access_valid;
    @(posedge clk)
    ibus_if_core0.bstart && !rst_n |-> |{ibus_if_mem0.ss, ibus_if_rom0.ss};
endproperty


//read_w: cover property (@(posedge clk) dbus_if_mem0.ttype == READ && dbus_if_mem0.tsize == WORD);
//read_h: cover property (@(posedge clk) dbus_if_mem0.ttype == READ && dbus_if_mem0.tsize == HALFWORD);
//read_b: cover property (@(posedge clk) dbus_if_mem0.ttype == READ && dbus_if_mem0.tsize == BYTE);
//write_w: cover property (@(posedge clk) dbus_if_mem0.ttype == WRITE && dbus_if_mem0.tsize == WORD);
//write_h: cover property (@(posedge clk) dbus_if_mem0.ttype == WRITE && dbus_if_mem0.tsize == HALFWORD);
//write_b: cover property (@(posedge clk) dbus_if_mem0.ttype == WRITE && dbus_if_mem0.tsize == BYTE);

assert property(dbus_access_valid) else $error("Accessing illegal D-bus address %h", dbus_if_core0.addr);
assert property(ibus_access_valid) else $error("Accessing illegal I-bus address %h", ibus_if_core0.addr);

initial forever #PERIOD clk = !clk;
initial #TIMEOUT $finish();

initial begin
    sysrst_n = 1;

    // reset
    #1;
    sysrst_n = 0;
    # 1;
    sysrst_n = 1;
end

initial begin
    // dump everything
    $dumpfile("dumpfile.fst");
    $dumpvars(0, top);

    // initialize ROM memory
    $readmemh("rom.mi", rom0.wrapped_mem.mem,0,250);

    // initialize RAM memory
    //$readmemh("memory.hex", mem0.wrapped_mem.mem,0,1000);
end

endmodule