int main () {
  unsigned int* flags = (unsigned int *)(0xA0);
  unsigned int* turn = (unsigned int *)(0xA8);
  unsigned int* counter = (unsigned int *)(0xAC);

  flags[1] = 1;
  *turn = 0;
  while (flags[0] == 1 && *turn == 0) { }

  *counter = *counter + 1;

  flags[1] = 0;

  return (*counter);
}

