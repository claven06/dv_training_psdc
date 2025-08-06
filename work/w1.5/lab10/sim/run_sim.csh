#!/bin/csh

# Type
if (! $?TYPE) then
    setenv TYPE "v"
endif

# Check to ensure at least 2 inputs
if (($#argv != 2) || ($1 == "")) then
    echo "[1] Usage: $0 <dv|idebug|pdebug|cov> <module_name>"
    exit 1
endif

# Check to ensure the valid 1st input
if (($1 != "dv") && ($1 != "idebug") && ($1 != "pdebug") && ($1 != "cov")) then
    echo "[2] Usage: $0 <dv|idebug|pdebug|cov> <module_name>"
    exit 1
endif

# Check to ensure the valid 2nd input
if (!(-e $ROOT/design/$2.$TYPE) || !(-e $ROOT/design/{$2}_tb.$TYPE)) then
    echo "[3] Usage: $0 <dv|idebug|pdebug|cov> <module_name>"
    exit 1
endif

# Run
setenv MODE $1
setenv MODULE $2
if (! $?STEP) then
    setenv STEP "2"
endif
if (! $?FLIST) then
    setenv FLIST "0"
endif
if (! $?MODULE_TB) then
    setenv MODULE_TB "$MODULE""_TB"
endif
if (! $?NR) then
    setenv NR "0"
endif

echo "[==== INFO ====] Running simulation: $0 $1 $2"
echo "[==== INFO ====] Run TYPE: $TYPE"
echo "[==== INFO ====] Run MODE: $MODE"
echo "[==== INFO ====] Run MODULE: $MODULE"
echo "[==== INFO ====] Run MODULE_TB: $MODULE_TB"
echo "[==== INFO ====] Run STEP: $STEP"
echo "[==== INFO ====] Run FLIST: $FLIST"
if ($FLIST == 1) then
    set filelist = "$ROOT/design/$MODULE.f"
    if (! -e $filelist) then
        echo "[4] ERROR: Filelist $filelist not found."
        exit 1
    endif
    set files = "-f $filelist"
else
    set files = "$ROOT/design/$MODULE.$TYPE $ROOT/design/$MODULE_TB.$TYPE"
endif

if ($MODE == "dv") then
    if ($STEP == 3) then
        echo "[==== INFO ====] vlogan -l $MODULE\_ana.log -sverilog -kdb $files"
        if ($NR != 1) then
            vlogan -l $MODULE\_ana.log -sverilog -kdb $files
        endif

        echo "[==== INFO ====] vcs -l $MODULE\_comp.log -sverilog -debug_access+all -kdb -debug_report -top $MODULE_TB -o $MODULE\_simv $files"
        if ($NR != 1) then
            vcs -l $MODULE\_comp.log -sverilog -debug_access+all -kdb -debug_report -top $MODULE_TB -o $MODULE\_simv $files
        endif

        echo "[==== INFO ====] $MODULE\_simv -l $MODULE\_sim.log"
        if ($NR != 1) then
            $MODULE\_simv -l $MODULE\_sim.log
        endif
    else
        echo "[==== INFO ====] vcs -l $MODULE\_comp.log -sverilog -debug_access+all -kdb -debug_report -top $MODULE_TB -o $MODULE\_simv $files"
        if ($NR != 1) then
            vcs -l $MODULE\_comp.log -sverilog -debug_access+all -kdb -debug_report -top $MODULE_TB -o $MODULE\_simv $files
        endif

        echo "[==== INFO ====] $MODULE\_simv -l $MODULE\_sim.log"
        if ($NR != 1) then
            $MODULE\_simv -l $MODULE\_sim.log
        endif
    endif
endif
