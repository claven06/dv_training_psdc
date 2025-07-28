#variables
VCS_OPTS = -sverilog
RUN_OPTS = -R 

#Grab the second word in the make command (e.g., the .sv file)
SRC      = $(filter %.sv, $(MAKECMDGOALS))

#target
all: build run

build:
	vcs $(VCS_OPTS) $(SRC) $(RUN_OPTS)

run:
#	./simv $(RUN_OPTS)

clean:
	rm -rf csrc simv simv.daidir ucli.key

# Dummy target to absorb extra argument (e.g., .sv)
%:
	@true

.PHONY: all build run clean

