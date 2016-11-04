int main () {
  unsigned int* enter = (unsigned int *)(0xA0);
  unsigned int* turn = (unsigned int*)(0xA8);
  unsigned int* counter = (unsigned int*)(0xAC);

  enter[0] = 1;
  while (enter[1] == 1) {
    if (*turn != 0) {
      enter[0] = 0;
      while (*turn != 0) { }
      enter[0] = 1;
    }
  }

  *counter = *counter + 1;

  *turn = 1;
  enter[0] = 0;

  return (*counter);
}
