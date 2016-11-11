struct __attribute__((device_builtin)) uint3 { unsigned int x, y, z; };
typedef __attribute__((device_builtin)) struct uint3 uint3;
struct __attribute__((device_builtin)) dim3 { unsigned int x, y, z; };
typedef __attribute__((device_builtin)) struct dim3 dim3;

uint3 __attribute__((device_builtin)) extern const threadIdx;
uint3 __attribute__((device_builtin)) extern const blockIdx;
dim3 __attribute__((device_builtin)) extern const blockDim;
dim3 __attribute__((device_builtin)) extern const gridDim;
int __attribute__((device_builtin)) extern const warpSize;

extern __attribute__((device)) __attribute__((device_builtin)) void __syncthreads(void);
__attribute__((global)) void uniform (int *a) {
  declare_postcondition("forall t : thread; forall t1 : thread;
        a[threadIdx.x@t] == a[threadIdx.x@t1]");

  int i = 0;
  a[threadIdx.x] = 0;
  
  while (i < 3) {
declare_invariant("forall t : thread; forall t1 : thread;
        i@t == i@t1", "forall t : thread; forall t1 : thread;
        a[threadIdx.x@t] == a[threadIdx.x@t1]");
    a[threadIdx.x]++;
    i++;
  }
}

__attribute__((global)) void mask (int *a) {
  declare_postcondition("a[0] == 0");
  a[threadIdx.x] = 0;
  if (threadIdx.x > 0) {
    while (a[threadIdx.x] == 0) {
      declare_invariant("a[0] == 0");
      a[threadIdx.x]++;
    }
  }
}

__attribute__((global)) void nonterm () {
  declare_postcondition("False");
  int i = 0;
    while (i == 0) {
declare_invariant("forall t : thread; i@t==0");;}
}


