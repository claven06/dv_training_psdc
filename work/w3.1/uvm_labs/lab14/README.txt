$ROOT
    |_    design/           // Directory that keeps lab14 design files
    |_    sim/              // Directory for running simulation, it contains makefile for running vcs flow(s)
    |_    lab14.setup       // Setup file that needs to be sourced at the very beginning, setting the environment related to this lab14
    |_    README.txt        // This file

% gtar -zxvf lab14.tar.gz    // Untar the file at your local area
% cd lab14
% source lab14.setup         // Change $ROOT to your local area
% cd sim
% make <sim_flow>

To perform the default vcs 2-step flow, use the following make command:
% make dv

To perform the default vcs 3-step flow, use the following make command:
% export STEP=3
% make dv
