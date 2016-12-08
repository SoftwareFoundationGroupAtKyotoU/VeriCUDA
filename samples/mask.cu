__global__ void uniform (int *a) {
  /*@ ensures \forall t : thread; \forall t1 : thread;
        a[threadIdx.x@t] == a[threadIdx.x@t1]; */
  int i = 0;
  a[threadIdx.x] = 0;
  /*@ loop invariant \forall t : thread; \forall t1 : thread;
        i@t == i@t1;
      loop invariant \forall t : thread; \forall t1 : thread;
        a[threadIdx.x@t] == a[threadIdx.x@t1]; */
  while (i < 3) {
    a[threadIdx.x]++;
    i++;
  }
}

__global__ void mask (int *a) {
  //@ ensures a[0] == 0
  a[threadIdx.x] = 0;
  if (threadIdx.x > 0) {
    while (a[threadIdx.x] == 0) {
      declare_invariant("a[0] == 0");
      a[threadIdx.x]++;
    }
  }
}

__global__ void nonterm () {
  //@ ensures False
  int i = 0;
  //@ loop invariant \forall t : thread; i@t==0;
  while (i == 0) {;}
}

