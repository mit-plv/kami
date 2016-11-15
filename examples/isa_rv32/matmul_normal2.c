#define MATRIX_SIZE 4
#define NUM_THREADS 4

int main()
{
  /*
   * - 0x000 -- 0x0FF: stack
   * - 0x100 -- 0x1FF: heap
   *   + 0x100 -- 0x13F: shared variables
   *   + 0x140 -- 0x17F: mat1
   *   + 0x180 -- 0x1BF: mat2
   *   + 0x1C0 -- 0x1FF: mres
   */
  volatile unsigned int* initd = (unsigned int *)(0x100); // single flag
  volatile unsigned int* finished = (unsigned int *)(0x104); // array of size #threads
  volatile unsigned int* mat1 = (unsigned int *)(0x140);
  volatile unsigned int* mat2 = (unsigned int *)(0x180);
  volatile unsigned int* mres = (unsigned int *)(0x1C0);

  // distributing the index for each thread
  unsigned int tidx = 2;

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

