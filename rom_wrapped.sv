// two ports, 1 Read only, other read and write
module rom_wrapped #(parameter int unsigned N = 1024) (
    slave_bus_if.slave bus,
    input bit clk
);

assign bus.bdone = 1'b1;

memory #(N) wrapped_mem (
    .data(bus.rdata),
    .data2(),
    .rerror(),
    .rerror2(),
    .werror(),
    .write_data(32'b0),
    .tsize(WORD),
    .clk(clk),
    .write(1'b0),
    .address(bus.addr[$clog2(N) - 1:0]),
    .address2({($clog2(N)){1'b0}})
);

endmodule