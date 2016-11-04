int main () {
  unsigned int* enter = (unsigned int *)(0xA0);
  unsigned int* turn = (unsigned int*)(0xA8);
  unsigned int* counter = (unsigned int*)(0xAC);

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
