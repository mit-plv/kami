/* 
 * fact.c: to calculate the factorial for a given unsigned integer [n].
 *
 * Expected output: 3628800
 */

int main () {
  unsigned int n, i;
  unsigned int factorial = 1;

  n = 10;

  for(i = 1; i <= n; ++i) {
    factorial *= i;
  }

  return factorial;
}
