int main () {
  unsigned int* flags = (unsigned int *)(0xA0);
  unsigned int* turn = (unsigned int *)(0xA8);
  unsigned int* counter = (unsigned int *)(0xAC);

  flags[0] = 1;
  *turn = 1;
  while (flags[1] == 1 && *turn == 1) { }

  *counter = *counter + 1;

  flags[0] = 0;

  return (*counter);
}

