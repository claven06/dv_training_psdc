clean:
	rm -rf csrc dump* DVEfiles simv simv.daidir ucli.key
	rm -rf novas* verdiLog

sim_fa: clean
	vcs -sverilog -R -debug_access+all -top tb_fa fa.sv tb_fa.sv

sim_mux2: clean
	vcs -sverilog -R -debug_access+all -top tb_mux2to1 mux2to1.sv tb_mux2to1.sv

sim_mux3: clean
	vcs -sverilog -R -debug_access+all -top tb_mux3to1 mux3to1.sv tb_mux3to1.sv

wave:
	dve -vpd dump.vpd &
	#verdi -ssf dump.fsdb &
