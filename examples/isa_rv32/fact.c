#include <stdio.h>

int main () {
  unsigned int n, i;
  unsigned int factorial = 1;

  n = 10;

  for(i = 1; i <= n; ++i) {
    factorial *= i;
  }

  return factorial;
}
