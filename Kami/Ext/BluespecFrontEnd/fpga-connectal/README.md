- On this directory, you can test a multicore+memory implementation on FPGA

Requirement
-----------

- A multicore+memory implementation: its filename should be `Proc.bsv`
  + Currently, `Host.bsv` and `SoftwareHost.cpp` are designed for 4 cores, but they can be redefined for n cores in a straightforward manner.
- Bluespec compiler
- Connectal framework

To build
--------

- Testing with the Bluespec simulation: `make build.bluesim`
- Testing on actual FPGA: `make build.vc707g2`

- Each build generates `(bluesim|vc707g2)/bin/ubuntu.exe`, we can simulate/execute just by running the executable.
