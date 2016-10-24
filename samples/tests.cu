void declare_precondition (void);
void declare_postcondition (void);
void declare_invariant (void);

void modify_param(int x) {
    declare_precondition("x==10");
    declare_postcondition("x == 11");
    x++;
}

void test1(unsigned int s) {
  declare_precondition("s > 0");
  declare_postcondition("s >= 0");
  s /= 2;
}
