/* 
 * hanoi.c: to solve the Hanoi tower puzzle using recursion.
 *
 * Expected output: 7
 */

unsigned int move_towers(unsigned int /* the number of tower blocks */,
			 unsigned int /* from */,
			 unsigned int /* to */,
			 unsigned int /* the other tower */);

/* NOTE: the main function should be _the first function_ defined in the
 * program. Unless the Kami processor wouldn't execute it correctly.
 */
int main()
{
  unsigned int num = 3; // number of tower blocks
  unsigned int moves;
  moves = move_towers(num, 0, 2, 1);

  return moves;
}

unsigned int move_towers(unsigned int num,
			 unsigned int frompeg,
			 unsigned int topeg,
			 unsigned int auxpeg) {
  if (num == 1) {
    return 1;
  }
    
  unsigned int moves1 = 0, moves2 = 0;
  moves1 = move_towers(num - 1, frompeg, auxpeg, topeg);
  moves2 = move_towers(num - 1, auxpeg, topeg, frompeg);

  return (moves1 + moves2 + 1);
}
