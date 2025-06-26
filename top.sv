module top;

// simulation clock period and timeout
localparam PERIOD = 5;
localparam TIMEOUT = 5000;

// master clk and master rst_n
bit clk, rst_n;

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
logic irq_sw0, irq_timer0;
rv_core #(.INITIAL_PC(32'h2000_0000)) core0(.ibus(ibus_if_core0), .dbus(dbus_if_core0), .clk(clk), .rst_n(rst_n), .irq_sw(irq_sw0), .irq_timer(irq_timer0));

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
    rst_n = 1;

    // reset
    #1;
    rst_n = 0;
    # 1;
    rst_n = 1;
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