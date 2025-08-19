package spi_pkg;
    `include "uvm_macros.svh"
    import uvm_pkg::*;

    `include "spi_tran.sv"
    `include "spi_seq.sv"
    `include "spi_sqr.sv"
    `include "spi_drv.sv"
    `include "spi_mon.sv"
    `include "spi_agt.sv"
    `include "spi_cov.sv"
    `include "spi_scb.sv"
    `include "spi_env.sv"
    `include "spi_base_test.sv"
    `include "spi_mosi_integrity_test.sv"
    `include "spi_reset_test.sv"
    `include "spi_clock_test.sv"
    //include other tests
endpackage
