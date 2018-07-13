/* 
 * matmul.c: Four threads try to calculate the matrix multiplication in
 * parallel. All threads do the computation for multiplication, while a
 * particular thread initializes the target matrices (operands) and 
 * another thread prints the trace of the resulting matrix.
 *
 * Expected outputs for each core:
 * - Core 0: 0
 * - Core 1: 0
 * - Core 2: 0
 * - Core 3: 16
 */

#ifndef THREAD_IDX
#error THREAD_IDX should be defined
#endif

#define MATRIX_SIZE 4
#define NUM_THREADS 4

/*
 * - 0x000 -- 0xBFF: program + stack
 *   + 0x000 -- 0x3FF: program
 *   + 0x400 -- 0x5FF: stack for the first thread
 *   + 0x600 -- 0x7FF: stack for the second thread
 *   + 0x800 -- 0x9FF: stack for the third thread
 *   + 0xA00 -- 0xBFF: stack for the fourth thread
 * - 0xC00 -- 0xCFF: heap
 *   + 0xC00 -- 0xC3F: shared variables
 *   + 0xC40 -- 0xC7F: mat1
 *   + 0xC80 -- 0xCBF: mat2
 *   + 0xCC0 -- 0xCFF: mres
 */
#define HEAP_STARTS_AT 0xC00

int main()
{
  volatile unsigned int* initd = (unsigned int *)(HEAP_STARTS_AT);
  volatile unsigned int* finished = (unsigned int *)(HEAP_STARTS_AT + 0x4);
  volatile unsigned int* mat1 = (unsigned int *)(HEAP_STARTS_AT + 0x40);
  volatile unsigned int* mat2 = (unsigned int *)(HEAP_STARTS_AT + 0x80);
  volatile unsigned int* mres = (unsigned int *)(HEAP_STARTS_AT + 0xC0);

  // Do nothing if already finished
  while (finished[THREAD_IDX] == 1) { }

  // Initialization (only for the core whose THREAD_IDX = 0)
#if THREAD_IDX == 0
  unsigned int a, b;
  for (a = 0; a < MATRIX_SIZE; a++) {
    for (b = 0; b < MATRIX_SIZE; b++) {
      mat1[a + MATRIX_SIZE * b] = (a == b) ? 2 : 0;
      mat2[a + MATRIX_SIZE * b] = (a == b) ? 2 : 0;
    }
  }
  
  // Initialization is done; time to calculate!
  *initd = 1;
#else
  // Other threads wait for the initialization
  while (*initd == 0) { }
#endif

  // Actual (parallel) matrix multiplication
  unsigned int i, j, k;
  for (i = 0; i < MATRIX_SIZE; i++) {
    for (j = THREAD_IDX; j < MATRIX_SIZE; j = j + NUM_THREADS) {
      for (k = 0; k < MATRIX_SIZE; k++) {
	mres[i + MATRIX_SIZE * j] = mres[i + MATRIX_SIZE * j]
	  + mat1[i + MATRIX_SIZE * k] * mat2[k + MATRIX_SIZE * j];
      }
    }
  }

  finished[THREAD_IDX] = 1;

#if THREAD_IDX == 3
  // Waiting for all the threads being finished
  unsigned int all_finished;
  while (1) {
    all_finished = 1;
    for (i = 0; i < NUM_THREADS; i++) {
      if (finished[i] == 0) {
	all_finished = 0;
	break;
      }
    }

    if (all_finished == 1)
      break;
  }

  // Ready to report the result!
  unsigned int tr = 0;
  for (i = 0; i < MATRIX_SIZE; i++) {
    tr = tr + mres[i + MATRIX_SIZE * i];
  }

  return tr;
#else
  return 0;
#endif
}
