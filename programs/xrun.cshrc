#!/bin/sh
## Cadence xrun setup 
## M.L. Johnston Jan 2025

set path = ($path /usr/local/apps/bin)

## PATHS FOR CADENCE DIGITAL VLSI CAD TOOLS 
setenv CDS_LIC_FILE 5280@linlic8.engr.oregonstate.edu
setenv CDS_AUTO_64BIT ALL

# XCelium HDL Simulation
setenv XCELIUM_HOME /usr/local/apps/cadence/xcelium/IUS2203
setenv PATH $XCELIUM_HOME/tools/bin:$PATH
setenv PATH $XCELIUM_HOME/tools/dfII/bin:$PATH
