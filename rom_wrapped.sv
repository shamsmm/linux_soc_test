// two ports, 1 Read only, other read and write
module rom_wrapped #(parameter int unsigned N = 1024) (
    slave_bus_if.slave bus,
    input bit clk,
    input bit rst_n
);

enum logic {AD, DO} state, next_state;

always_ff @(posedge clk, negedge rst_n)
    if (!rst_n)
        state <= AD;
    else    
        state <= next_state;

always_comb begin
    case(state)
        AD: next_state = bus.bstart ? DO : AD;
        DO: next_state = AD;
    endcase
end

always_comb begin
    bus.bdone = 0;
    case(state)
        AD: bus.bdone = 0;
        DO: bus.bdone = 1;
    endcase
end

memory_word #(N) wrapped_mem (
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