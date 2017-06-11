/* 
 * peterson1.c: two threads (the other thread by [peterson2.c]) try to increase
 * the shared counter concurrently, using the Peterson's algorithm.
 *
 * Expected outputs: (increasing counter sequence from zero)
 */

/*
 * - 0x000 -- 0xBFF: program + stack
 * - 0xC00 -- : heap
 */
#define HEAP_STARTS_AT 0xC00

int main () {
  unsigned int* flags = (unsigned int *)(HEAP_STARTS_AT);
  unsigned int* turn = (unsigned int *)(HEAP_STARTS_AT + 0x8);
  unsigned int* counter = (unsigned int *)(HEAP_STARTS_AT + 0xC);

  flags[0] = 1;
  *turn = 1;
  while (flags[1] == 1 && *turn == 1) { }

  *counter = *counter + 1;

  flags[0] = 0;

  return (*counter);
}

