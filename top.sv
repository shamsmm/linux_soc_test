module top;

localparam PERIOD = 5;
localparam TIMEOUT = 1000;

bit clk, rst_n;

master_bus_if dbus_if_core0(clk, rst_n);
master_bus_if ibus_if_core0(clk, rst_n);

slave_bus_if dbus_if_mem0(clk, rst_n);
slave_bus_if ibus_if_mem0(clk, rst_n);

rv_core #(.INITIAL_PC(32'hF000_0000)) core0(.ibus(ibus_if_core0), .dbus(dbus_if_core0), .clk(clk), .rst_n(rst_n));
memory_wrapped mem0(.ibus(ibus_if_mem0), .dbus(dbus_if_mem0), .clk(clk));

property dbus_access_valid;
    @(posedge clk)
    dbus_if_core0.bstart |-> dbus_if_mem0.ic.ss;
endproperty

property ibus_access_valid;
    @(posedge clk)
    ibus_if_core0.bstart |-> ibus_if_mem0.ic.ss;
endproperty

assert property(dbus_access_valid) else $error("Accessing illegal D-bus address %h", dbus_if_core0.addr);
assert property(ibus_access_valid) else $error("Accessing illegal I-bus address %h", ibus_if_core0.addr);

always_comb begin
    // default bus values
    dbus_if_core0.ic.rdata = 32'b0;
    dbus_if_core0.ic.berror = 1'b0;
    dbus_if_core0.ic.bdone = 1'b0;
    dbus_if_core0.ic.bgnt = dbus_if_core0.ic.breq; // always grant (no contention)

    dbus_if_mem0.ic.ss = 1'b0;
    //dbus_if_sram0.ic.ss = 1'b0;
    //dbus_if_uart0.ic.ss = 1'b0;

    // connect to bus
    dbus_if_mem0.ic.wdata = dbus_if_core0.ic.wdata;
    dbus_if_mem0.ic.addr = dbus_if_core0.ic.addr;
    dbus_if_mem0.ic.tsize = dbus_if_core0.ic.tsize;
    dbus_if_mem0.ic.bstart = dbus_if_core0.ic.bstart;

    // poor man's multiplexor
    case(dbus_if_core0.ic.addr[31:28])
        4'hF: begin
            dbus_if_core0.ic.bdone = dbus_if_mem0.ic.bdone;
            dbus_if_core0.ic.rdata = dbus_if_mem0.ic.rdata;
            dbus_if_mem0.ic.ss = 1'b1;
        end
        // other
    endcase
end

always_comb begin
    // default bus values
    ibus_if_core0.ic.rdata = 32'b0;
    ibus_if_core0.ic.berror = 1'b0;
    ibus_if_core0.ic.bdone = 1'b0;
    ibus_if_core0.ic.bgnt = ibus_if_core0.ic.breq; // always grant (no contention)

    ibus_if_mem0.ic.ss = 1'b0;

    // connect to bus
    ibus_if_mem0.ic.wdata = ibus_if_core0.ic.wdata;
    ibus_if_mem0.ic.addr = ibus_if_core0.ic.addr;
    ibus_if_mem0.ic.tsize = ibus_if_core0.ic.tsize;
    ibus_if_mem0.ic.bstart = ibus_if_core0.ic.bstart;

    // poor man's multiplexor
    case(ibus_if_core0.ic.addr[31:28])
        4'hF: begin
            ibus_if_core0.ic.bdone = ibus_if_mem0.ic.bdone;
            ibus_if_core0.ic.rdata = ibus_if_mem0.ic.rdata;
            ibus_if_mem0.ic.ss = 1'b1;
        end
        // crossbar
    endcase
end

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


    // initialize memory
    $readmemh("memory.hex", mem0.wrapped_mem.mem,0,1000);
end

endmodule