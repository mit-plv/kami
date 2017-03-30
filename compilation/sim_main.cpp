#include "verilated.h"
#include "Vtop.h"
#include <iostream>

int main(int argc, char ** argv, char **env) {
  Verilated::commandArgs(argc, argv);
  Vtop* top = new Vtop;

  vluint64_t main_time = 0;

  top->RESET = 1;
  while (!Verilated::gotFinish()) {
    top->CLK = main_time%2;
    if (main_time > 10)
      top->RESET = 0;
    top->eval();
    main_time++;
  }
  top->final();
  delete top;
  return 0;
}
