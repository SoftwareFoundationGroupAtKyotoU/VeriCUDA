void declare_precondition (void);
void declare_postcondition (void);
void declare_invariant (void);

void count_up() {
    declare_postcondition("x == 11");
    int x = 0;
    while (x <= 10) {
        declare_invariant("x <= 11");
        x++;
    }
}

