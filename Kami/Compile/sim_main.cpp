#include "verilated.h"
#include "Vtop.h"
#include <iostream>

#include "verilated_vcd_c.h"

int main(int argc, char ** argv, char **env) {
  Verilated::commandArgs(argc, argv);
  Verilated::traceEverOn(true);

  Vtop* top = new Vtop;
  VerilatedVcdC* tfp = new VerilatedVcdC;
  top->trace(tfp,99);
  tfp->open("trace.vcd");
  
  vluint64_t main_time = 0;

  top->RESET_N = 0;
  while (!Verilated::gotFinish()) {
    top->toHost__024a__024_g = 1;
    top->toHost__024aa__024_g = 1;
    top->toHost__024aaa__024_g = 1;
    top->toHost__024aaaa__024_g = 1;

    top->toHost__024a__024_ret = 1;
    top->toHost__024aa__024_ret = 1;
    top->toHost__024aaa__024_ret = 1;
    top->toHost__024aaaa__024_ret = 1;

    top->CLK = main_time%2;
    if (main_time > 10)
      top->RESET_N = 1;
    top->eval();

    //std :: cout << "clk: " << main_time / 2 << endl;

    if(top->CLK == 1) {
      if(top->toHost__024a__024_en == 1)
        std :: cout << main_time/2 << " 0: " << top->toHost__024a__024_arg << std :: endl;

      if(top->toHost__024aa__024_en == 1)
        std :: cout << main_time/2 << " 1: " << top->toHost__024aa__024_arg << std :: endl;

      if(top->toHost__024aaa__024_en == 1)
        std :: cout << main_time/2 << " 2: " << top->toHost__024aaa__024_arg << std :: endl;

      if(top->toHost__024aaaa__024_en == 1)
        std :: cout << main_time/2 << " 3: " << top->toHost__024aaaa__024_arg << std :: endl;
    }

    //tfp->dump(main_time);

    main_time++;
  }
  top->final();
  tfp->close();
  delete top;
  delete tfp;
  return 0;
}
