/* 
 * peterson2.c: two threads (the other thread by [peterson1.c]) try to increase
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

  flags[1] = 1;
  *turn = 0;
  while (flags[0] == 1 && *turn == 0) { }

  *counter = *counter + 1;

  flags[1] = 0;

  return (*counter);
}

