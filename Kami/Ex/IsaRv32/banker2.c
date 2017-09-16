/* 
 * banker.c: four threads simulate the concurrent bank transactions. We have
 * some deposits and a number of transaction requests. Each thread tries to take
 * a request from the request pool and to execute the transaction. Careful
 * locking is certainly required for such concurrent transactions.
 *
 * Expected output: the thread which handles the last transaction request should
 * print "11000".
 */

/*
 * - 0x000 -- 0xBFF: program + stack
 *   + 0x000 -- 0x3FF: program
 *   + 0x400 -- 0x5FF: stack for the first thread
 *   + 0x600 -- 0x7FF: stack for the second thread
 *   + 0x800 -- 0x9FF: stack for the third thread
 *   + 0xA00 -- 0xBFF: stack for the fourth thread
 * - 0xC00 -- : heap
 */
#define HEAP_STARTS_AT 0xC00

#define NUM_DEPOSITS 2
#define NUM_REQUESTS 10
#define NUM_THREADS 4
#define TID 2

int main()
{
  volatile unsigned int* deposits = (unsigned int *)(HEAP_STARTS_AT); // 2 * 4
  volatile unsigned int* deposit_locks = (unsigned int *)(HEAP_STARTS_AT + 0x8); // 2 * 4

  volatile unsigned int* high_flags = (unsigned int *)(HEAP_STARTS_AT + 0x10); // 4 * 4
  volatile unsigned int* low_flags = (unsigned int *)(HEAP_STARTS_AT + 0x20); // 4 * 4
  volatile unsigned int* high_turns = (unsigned int *)(HEAP_STARTS_AT + 0x30); // 4 * 4
  volatile unsigned int* low_turns = (unsigned int *)(HEAP_STARTS_AT + 0x40); // 4 * 4

  volatile unsigned int* from_requests = (unsigned int *)(HEAP_STARTS_AT + 0x50); // 10 * 4 == 0x28
  volatile unsigned int* to_requests = (unsigned int *)(HEAP_STARTS_AT + 0x78); // 10 * 4 == 0x28
  volatile unsigned int* amt_requests = (unsigned int *)(HEAP_STARTS_AT + 0xA0); // 10 * 4 == 0x28
  
  volatile unsigned int* cur_request = (unsigned int *)(HEAP_STARTS_AT + 0xC8); // 4

  volatile unsigned int* request_flags = (unsigned int *)(HEAP_STARTS_AT + 0xCC); // 4 * 4
  volatile unsigned int* request_turns = (unsigned int *)(HEAP_STARTS_AT + 0xDC); // 4 * 4

  volatile unsigned int* init = (unsigned int *)(HEAP_STARTS_AT + 0xEC);

  // initialization for anything
  unsigned int i;
  if (TID == 0) {
    // For deposits
    for (i = 0; i < NUM_DEPOSITS; i++) {
      deposits[i] = 10000;
    }

   // For requests
    for (i = 0; i < NUM_REQUESTS; i++) {
      from_requests[i] = 0;
      to_requests[i] = 1;
      amt_requests[i] = 100;
    }
    
    *init = 1;
  }

  while (*init == 0) { }

  if (*cur_request == NUM_REQUESTS)
    while (1) { }

  while (1) {

    // 1) get the current request
    unsigned int j, k, br;
    for (j = 0; j < NUM_THREADS - 1; j++) {
      request_flags[TID] = j + 1;
      request_turns[j] = TID;

      while (1) {
	if (request_turns[j] != TID) break;

	br = 1;
	for (k = 0; k < NUM_THREADS; k++)
	  if (k != TID && request_flags[k] >= j + 1)
	    br = 0;

	if (br == 1) break;
      }
    }

    unsigned int my_request_from = from_requests[*cur_request];
    unsigned int my_request_to = to_requests[*cur_request];
    unsigned int my_request_amt = amt_requests[*cur_request];
    unsigned int requests_done = (*cur_request == NUM_REQUESTS) ? 1 : 0;
    if (requests_done == 0)
      *cur_request = *cur_request + 1;

    // CS for requests ends

    request_flags[TID] = 0;

    // If all requests are done, break the loop
    if (requests_done == 1) break;

    // 2) get the lock for the higher
    for (j = 0; j < NUM_THREADS - 1; j++) {
      high_flags[TID] = j + 1;
      high_turns[j] = TID;

      while (1) {
	if (high_turns[j] != TID) break;

	br = 1;
	for (k = 0; k < NUM_THREADS; k++)
	  if (k != TID && high_flags[k] >= j + 1)
	    br = 0;

	if (br == 1) break;
      }
    }

    unsigned int higher = my_request_from > my_request_to
      ? my_request_from
      : my_request_to;
    while (deposit_locks[higher] == 1) { }

    deposit_locks[higher] = 1;

    high_flags[TID] = 0;

    // 3) get the lock for the lower
    for (j = 0; j < NUM_THREADS - 1; j++) {
      low_flags[TID] = j + 1;
      low_turns[j] = TID;

      while (1) {
	if (low_turns[j] != TID) break;

	br = 1;
	for (k = 0; k < NUM_THREADS; k++)
	  if (k != TID && low_flags[k] >= j + 1)
	    br = 0;

	if (br == 1) break;
      }
    }

    unsigned int lower = my_request_from > my_request_to
      ? my_request_to
      : my_request_from;
    while (deposit_locks[lower] == 1) { }

    deposit_locks[lower] = 1;

    low_flags[TID] = 0;

    // 4) make a transaction

    deposits[my_request_from] = deposits[my_request_from] - my_request_amt;
    deposits[my_request_to] = deposits[my_request_to] + my_request_amt;

    // 5) release deposit locks

    deposit_locks[higher] = 0;
    deposit_locks[lower] = 0;

  }

  return deposits[1];
}
