__global__ void count_up() {
  //@ ensures x == 11
  int x = 0;
  //@ loop invariant x <= 11
  while (x <= 10) {
    x++;
  }
}
