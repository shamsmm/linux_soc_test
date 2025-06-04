SOURCE = ../src/rv_core

FILES = $(wildcard $(SOURCE)/*.sv)
FILES += memory.sv memory_wrapped.sv top.sv

# skip warning if needed
VERILATOR_OPTIONS=-Wno-UNOPTFLAT -Wno-CASEINCOMPLETE

# do not optimize because ordering and register values go booom
RV32_ASSEMBLE_OPTIONS=-O0

all: visualize

visualize: simulate
	gtkwave dumpfile.fst

simulate: compile
	./obj_dir/test

compile:
	verilator --binary -j 0 -o test --top-module top +incdir+$(SOURCE) $(FILES) $(VERILATOR_OPTIONS) --trace-fst --trace-structs --timescale 1ns/1ns

generate:
	riscv32-unknown-elf-as $(RV32_ASSEMBLE_OPTIONS) -march=rv32i -mabi=ilp32 -mlittle-endian -o test.elf test.asm
	riscv32-unknown-elf-objcopy -O binary --pad-to=1024 --gap-fill=0x00 test.elf test.bin
	xxd -p -c 1 test.bin > memory.hex

clean:
	rm -f test.fst test.vvp test.elf irom.bin
