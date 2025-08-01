#variables
VCS_OPTS = -sverilog -kdb -debug_access+all
RUN_OPTS = -R 
FUNC_CVR = -cm line+cond+tgl+fsm+branch+assert
FILE_TO_DEL = csrc simv simv.daidir ucli.key libnz4w_r.soLog verdiLog \
verdi_config_file inter.fsdb dump.vcd novas* cm.log simv.vdb urgReport \
vdCov.conf vdCovLog

#Grab the second word in the make command (e.g., the .sv file)
#SRC      = $(filter %.sv, $(MAKECMDGOALS))
SRC		  = -f ./build.f

#target
all: build run

build:
	vcs $(SRC) $(VCS_OPTS) $(FUNC_CVR) 

run:
	./simv $(FUNC_CVR) 

#To generate coverage reports and analyze the results
#using Unified Report Generator 
urgcov:
	urg -dir simv.vdb

# using Verdi Coverage GUI
verdicov:
	verdi -cov -covdir simv.vdb &

clean:
	rm -rf $(FILE_TO_DEL) 

# Dummy target to absorb extra argument (e.g., .sv)
%:
	@true

.PHONY: all build run clean

