struct __attribute__((device_builtin)) uint3
{
    unsigned int x, y, z;
};
typedef __attribute__((device_builtin)) struct uint3 uint3;

struct __attribute__((device_builtin)) dim3
{
    unsigned int x, y, z;

//    __attribute__((host)) __attribute__((device)) dim3(unsigned int vx = 1, unsigned int vy = 1, unsigned int vz = 1) : x(vx), y(vy), z(vz) {}
//    __attribute__((host)) __attribute__((device)) dim3(uint3 v) : x(v.x), y(v.y), z(v.z) {}
//    __attribute__((host)) __attribute__((device)) operator uint3(void) { uint3 t; t.x = x; t.y = y; t.z = z; return t; }

};
typedef __attribute__((device_builtin)) struct dim3 dim3;

uint3 __attribute__((device_builtin)) extern const threadIdx;
uint3 __attribute__((device_builtin)) extern const blockIdx;
dim3 __attribute__((device_builtin)) extern const blockDim;
dim3 __attribute__((device_builtin)) extern const gridDim;
int __attribute__((device_builtin)) extern const warpSize;

extern __attribute__((device)) __attribute__((device_builtin)) void __syncthreads(void);
/* #include <stdio.h> */
/* #include <stdlib.h> */
/* #include <math.h> */
/* #include "ido.h" */


void uniform (int *a) {
    declare_postcondition(
        "forall t : thread. forall t1 : thread.
                a[threadIdx.x@t] == a[threadIdx.x@t1]"
        );
    int i = 0;
    a[threadIdx.x] = 0;
    while (i < 3) {
        declare_invariant(
            "forall t : thread. forall t1 : thread. i@t == i@t1",
            "forall t : thread. forall t1 : thread.
                a[threadIdx.x@t] == a[threadIdx.x@t1]"
            );
        a[threadIdx.x]++;
        i++;
    }
}

/* not provable with --no-inline */
void mask (int *a) {
    // declare_precondition("blockDim.x > 1");
    declare_postcondition("a[0] == 0");
    a[threadIdx.x] = 0;
    if (threadIdx.x > 0) {
        while (a[threadIdx.x] == 0) {
            declare_invariant("a[0] == 0");
            a[threadIdx.x]++;
        }
    }
}


/* not provable with --no-inline --no-transform */
void nonterm () {
    declare_postcondition("False");
    int i = 0;
    while (i == 0) {
        declare_invariant("forall t : thread. i@t==0");
    }
}

