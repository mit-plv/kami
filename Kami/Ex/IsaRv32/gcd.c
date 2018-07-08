/* 
 * gcd.c: to calculate the greatest common divisor for given two unsigned
 * integers [n1] and [n2], based on the Euclidean algorithm.
 *
 * Expected output: 6
 */

int main()
{
  unsigned int n1, n2;

  n1 = 12;
  n2 = 18;
    
  while (n1 != n2) {
    if (n1 > n2)
      n1 -= n2;
    else
      n2 -= n1;
  }

  return n1;
}
