void modify_param(int x) {
  /*@ requires x == 10;
      ensures x == 11; */
  x++;
}

void test1(unsigned int s) {
  /*@ requires s > 0;
      ensures s >= 0; */
  s /= 2;
}
