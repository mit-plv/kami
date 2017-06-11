/* 
 * dekker2.c: two threads (the other thread by [dekker1.c]) try to increase the
 * shared counter concurrently, using the Dekker's algorithm.
 *
 * Expected outputs: (increasing counter sequence from zero)
 */

/*
 * - 0x000 -- 0xBFF: program + stack
 * - 0xC00 -- : heap
 */
#define HEAP_STARTS_AT 0xC00

int main () {
  unsigned int* enter = (unsigned int *)(HEAP_STARTS_AT);
  unsigned int* turn = (unsigned int*)(HEAP_STARTS_AT + 0x8);
  unsigned int* counter = (unsigned int*)(HEAP_STARTS_AT + 0xC);

  enter[1] = 1;
  while (enter[0] == 1) {
    if (*turn != 1) {
      enter[1] = 0;
      while (*turn != 1) { }
      enter[1] = 1;
    }
  }

  *counter = *counter + 1;

  *turn = 0;
  enter[1] = 0;

  return (*counter);
}
