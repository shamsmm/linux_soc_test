RVCORE_SOURCE = ../src/rv_core
IC_SOURCE = ../src/interconnect
FILES = ../src/rv_core/bus_if_types_pkg.sv
FILES += ../src/rv_core/instructions.sv
FILES += ../src/jtag.sv
FILES += ../src/dtm_jtag.sv
FILES += $(filter-out ../src/rv_core/instructions.sv, $(filter-out ../src/rv_core/bus_if_types_pkg.sv, $(wildcard $(RVCORE_SOURCE)/*.sv)))
FILES += $(wildcard $(IC_SOURCE)/*.sv)
FILES += memory.sv memory_word.sv memory_wrapped.sv rom_wrapped.sv gpio_wrapped.sv top.sv jtag_test.sv

#TOP_MODULE=top
#ASM_TO_COMPILE=test2.asm
#C_SRC =
#AS_SRC = test6.asm
include Makefile.local # if it is not present then override TOP_MODULE directly and comment this line

# skip warning if needed
VERILATOR_OPTIONS=-Wno-CASEINCOMPLETE

# Assemble, Compile and Link
CC = riscv32-unknown-elf-
OBJS_DIR = test_code_build
TEST_CODE_NAME = test
LINKER = minimal_soc.ld
COBJ := $(addprefix $(OBJS_DIR)/, $(notdir $(C_SRC:.c=.o)))
ASOBJ := $(addprefix $(OBJS_DIR)/, $(notdir $(AS_SRC:.asm=.o)))

all: visualize

visualize: simulate
	gtkwave dumpfile.fst

simulate: compile
	./obj_dir/test

coverage: simulate
	verilator_coverage -write-info coverage.info coverage.dat
	genhtml coverage.info --output-directory html_coverage_report

compile: gcc
	verilator --binary -j 0 -o test --top-module $(TOP_MODULE) +incdir+$(RVCORE_SOURCE) +incdir+$(IC_SOURCE) $(FILES) $(VERILATOR_OPTIONS) --trace-fst --trace-structs --trace-params --assert --timescale 1ns/1ns --coverage

# Single file asm, no linking or c code
generate:
	riscv32-unknown-elf-as -march=rv32i_zicsr -mabi=ilp32 -mlittle-endian -o test.elf $(ASM_TO_COMPILE)
	riscv32-unknown-elf-objcopy -O binary --pad-to=1024 --gap-fill=0x00 test.elf test.bin
	xxd -p -c 1 test.bin > rom.hex
	echo -e "#File_format=Hex\n#Address_depth=1024\n#Data_width=32" > rom.mi
	xxd -e test.bin | xxd -r > test_be.bin
	xxd -p -c 4 test_be.bin >> rom.mi

gcc: build_dir rom.mi

rom.mi: $(TEST_CODE_NAME).elf
	riscv32-unknown-elf-objcopy -O binary --pad-to=1024 --gap-fill=0x00 -j .text $< test.bin
	echo -e "#File_format=Hex\n#Address_depth=1024\n#Data_width=32" > $@
	xxd -e test.bin | xxd -r > test_be.bin
	xxd -p -c 4 test_be.bin >> $@

$(TEST_CODE_NAME).elf: $(COBJ) $(ASOBJ) $(LINKER)
	$(CC)gcc -march=rv32i_zicsr -mabi=ilp32 -mlittle-endian -O0 -nostdlib -T$(LINKER) $(COBJ) $(ASOBJ) -o $@

$(OBJS_DIR)/%.o: %.c
	$(CC)gcc -march=rv32i_zicsr -mabi=ilp32 -mlittle-endian $< -c -nostdlib $(INCS) -o $@  $(CFLAGS)

$(OBJS_DIR)/%.o: %.asm
	$(CC)as -march=rv32i_zicsr -mabi=ilp32 -mlittle-endian $< -o $@ 

build_dir:
	mkdir -p $(OBJS_DIR)

clean:
	rm -f test.fst test.vvp test.elf irom.bin rom.mi $(TEST_CODE_NAME).elf