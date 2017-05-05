/* 
 * bsort.c: to sort a given unsigned integer array [targets] by using the bubble
 * sort algorithm.
 *
 * Expected output: 349
 */

int main () {
  unsigned int targets[] = {4, 20, 120, 53, 24, 349, 29, 83, 126, 78};
  unsigned int i, j, tmp;

  for (i = 0; i < 9; i++) {
    for (j = 0; j < 9 - i; j++) {
      if (targets[j] > targets[j+1]) {
	tmp = targets[j];
	targets[j] = targets[j+1];
	targets[j+1] = tmp;
      }
    }
  }

  return targets[9];
}
