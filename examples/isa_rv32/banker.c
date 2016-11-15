#define NUM_DEPOSITS 2
#define NUM_REQUESTS 10
#define NUM_THREADS 4
#define TID 0

int main()
{
  /*
   * - 0x000 -- 0x0FF: stack
   * - 0x100 -- 0x1FF: heap
   */
  volatile unsigned int* deposits = (unsigned int *)(0x100); // 2 * 4
  volatile unsigned int* deposit_locks = (unsigned int *)(0x108); // 2 * 4

  volatile unsigned int* high_flags = (unsigned int *)(0x110); // 4 * 4
  volatile unsigned int* low_flags = (unsigned int *)(0x120); // 4 * 4
  volatile unsigned int* high_turns = (unsigned int *)(0x130); // 4 * 4
  volatile unsigned int* low_turns = (unsigned int *)(0x140); // 4 * 4

  volatile unsigned int* from_requests = (unsigned int *)(0x150); // 10 * 4 == 0x28
  volatile unsigned int* to_requests = (unsigned int *)(0x178); // 10 * 4 == 0x28
  volatile unsigned int* amt_requests = (unsigned int *)(0x1A0); // 10 * 4 == 0x28
  
  volatile unsigned int* cur_request = (unsigned int *)(0x1C8); // 4

  volatile unsigned int* request_flags = (unsigned int *)(0x1CC); // 4 * 4
  volatile unsigned int* request_turns = (unsigned int *)(0x1DC); // 4 * 4

  volatile unsigned int* init = (unsigned int *)(0x1EC);

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
