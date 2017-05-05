/* 
 * matmul_normal1.c: four threads try to calculate the matrix multiplication in
 * parallel. We test this multiplication by printing the trace of the result
 * matrix, which is done by [matmul_report.c]
 *
 * Expected output: 0
 */

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
  volatile unsigned int* initd = (unsigned int *)(HEAP_STARTS_AT); // single flag
  volatile unsigned int* finished = (unsigned int *)(HEAP_STARTS_AT + 0x4); // array of size #threads
  volatile unsigned int* mat1 = (unsigned int *)(HEAP_STARTS_AT + 0x40);
  volatile unsigned int* mat2 = (unsigned int *)(HEAP_STARTS_AT + 0x80);
  volatile unsigned int* mres = (unsigned int *)(HEAP_STARTS_AT + 0xC0);

  // distributing the index for each thread
  unsigned int tidx = 1;

  // do nothing if already finished
  while (finished[tidx] == 1) { }

  // waiting for initialization
  while (*initd == 0) { }

  unsigned int i, j, k;
  for (i = 0; i < MATRIX_SIZE; i++) {
    for (j = tidx; j < MATRIX_SIZE; j = j + NUM_THREADS) { // #threads used here
      for (k = 0; k < MATRIX_SIZE; k++) {
	mres[i + MATRIX_SIZE * j] = mres[i + MATRIX_SIZE * j]
	  + mat1[i + MATRIX_SIZE * k] * mat2[k + MATRIX_SIZE * j];
      }
    }
  }

  // partial multiplication done!
  finished[tidx] = 1;

  return 0;
}

