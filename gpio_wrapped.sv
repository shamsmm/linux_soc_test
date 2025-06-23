// byte accessed, 4-byte aligned 8-bit gpio
// TODO: interrupts
module gpio_wrapped(slave_bus_if.slave bus, input bit clk);

// simulate gpio
logic [7:0] pins;
assign pins = {8'bZZ0ZZZ1Z} | (output_val & output_en);

logic [7:0] input_val;
logic [7:0] input_en;
logic [7:0] output_en;
logic [7:0] output_val;

always_comb begin
    bus.bdone = 1'b1; // all thing take one clock cycle
    input_val = pins & input_en;

    case(bus.addr[7:0])
        8'h00: bus.rdata = {24'b0, input_val};
        8'h04: bus.rdata = {24'b0, input_en};
        8'h08: bus.rdata = {24'b0, output_en};
        8'h0C: bus.rdata = {24'b0, output_val};
    endcase
end

always_ff @( posedge clk ) begin
    if (bus.ss) begin
        case(bus.addr[7:0])
            8'h04: input_en <= bus.wdata[7:0];
            8'h08: output_en <= bus.wdata[7:0];
            8'h0C: output_val <= bus.wdata[7:0];
        endcase
    end
end

endmodule