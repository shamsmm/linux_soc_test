SOURCE = ../src/rv_core

FILES = $(wildcard $(SOURCE)/*.sv)
FILES += memory.sv memory_wrapped.sv top.sv

VERILATOR_OPTIONS=-Wno-WIDTH -Wno-IMPLICIT -Wno-WIDTHCONCAT -Wno-WIDTHEXPAND -Wno-WIDTHTRUNC -Wno-UNOPTFLAT -Wno-CASEINCOMPLETE -Wno-LATCH

all: visualize

visualize: simulate
	gtkwave dumpfile.fst

simulate: compile
	./obj_dir/test

compile:
	verilator --binary -j 0 -o test --top-module top +incdir+$(SOURCE) $(FILES) $(VERILATOR_OPTIONS) --trace-fst --timescale 1ns/1ns

clean:
	rm -f test.fst test.vvp test.elf irom.bin
