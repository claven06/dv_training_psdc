#variables
VCS_OPTS = -sverilog -kdb -debug_access+all
RUN_OPTS = -R 
FILE_TO_DEL = csrc simv simv.daidir ucli.key libnz4w_r.soLog verdiLog \
verdi_config_file inter.fsdb dump.vcd novas*

#Grab the second word in the make command (e.g., the .sv file)
#SRC      = $(filter %.sv, $(MAKECMDGOALS))
SRC		  = -f dff.f
#target
all: build run

build:
	vcs $(SRC) $(VCS_OPTS) $(RUN_OPTS)

run:
#	./simv $(RUN_OPTS)

clean:
	rm -rf $(FILE_TO_DEL) 

# Dummy target to absorb extra argument (e.g., .sv)
%:
	@true

.PHONY: all build run clean

