RVCORE_SOURCE = ../src/rv_core
IC_SOURCE = ../src/interconnect
FILES = $(wildcard $(RVCORE_SOURCE)/*.sv)
FILES += $(wildcard $(IC_SOURCE)/*.sv)
FILES += memory.sv memory_wrapped.sv rom_wrapped.sv top.sv

# skip warning if needed
VERILATOR_OPTIONS=-Wno-UNOPTFLAT -Wno-CASEINCOMPLETE

all: visualize

visualize: simulate
	gtkwave dumpfile.fst

simulate: compile
	./obj_dir/test

compile: generate
	verilator --binary -j 0 -o test --top-module top +incdir+$(RVCORE_SOURCE) +incdir+$(IC_SOURCE) $(FILES) $(VERILATOR_OPTIONS) --trace-fst --trace-structs --trace-params --assert --timescale 1ns/1ns

generate: test.asm
	riscv32-unknown-elf-as -march=rv32i -mabi=ilp32 -mlittle-endian -o test.elf test.asm
	riscv32-unknown-elf-objcopy -O binary --pad-to=1024 --gap-fill=0x00 test.elf test.bin
	xxd -p -c 1 test.bin > rom.hex

clean:
	rm -f test.fst test.vvp test.elf irom.bin
