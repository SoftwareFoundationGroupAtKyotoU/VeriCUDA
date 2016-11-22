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


#define  blockDim_x     256
#define  blockDim_y       8


/* __global__ */
void  diffusion1d_naive (
   float    *f,         /* dependent variable                        */
   float    *fn,        /* dependent variable                        */
   int      n,          /* grid number in the x-direction            */
   float    c0,         /* coefficient no.0                          */
   float    c1          /* coefficient no.1                          */
)
{
    declare_precondition(
        "n == blockDim.x * gridDim.x",
        "n > 1"
        );
    declare_postcondition(
        "fn[0] == c0 * (f[0] + f[1]) + c1 * f[0]",
        "fn[n - 1] == c0 * (f[n - 2] + f[n - 1]) + c1 * f[n - 1]",
        "forall j. 0 < j -> j < n - 1 ->
            fn[j] == c0 * (f[j - 1] + f[j + 1]) + c1 * f[j]"
        );

    int    j;
    float  fcc,  fce,  fcw;

    j = blockDim.x*blockIdx.x + threadIdx.x;

    fcc = f[j];

    if(j == 0) fcw = fcc;
    else       fcw = f[j - 1];

    if(j == n - 1) fce = fcc;
    else           fce = f[j+1];

    fn[j] = c0*(fcw + fce) + c1*fcc;
}

void diffusion1d(float *f, float *fn, int n, float c0, float c1)
{
    declare_precondition(
        "n == blockDim.x * gridDim.x",
        "n > 1"
        );
    declare_postcondition(
        "fn[0] == c0 * (f[0] + f[1]) + c1 * f[0]",
        "fn[n - 1] == c0 * (f[n - 2] + f[n - 1]) + c1 * f[n - 1]",
        "forall j. 0 < j -> j < n - 1 ->
            fn[j] == c0 * (f[j - 1] + f[j + 1]) + c1 * f[j]"
        );

    __attribute__((shared)) float fs[];
    
    fs[threadIdx.x + 1] = f[blockDim.x * blockIdx.x + threadIdx.x];

    if(threadIdx.x == 0) {
        fs[0] =
            (blockIdx.x == 0) ?
            fs[1] :
            f[blockDim.x * blockIdx.x + threadIdx.x-1];
    }
    if(threadIdx.x == blockDim.x - 1) {
        fs[threadIdx.x + 2] =
            (blockIdx.x == gridDim.x - 1) ?
            fs[threadIdx.x + 1] :
            f[blockDim.x * blockIdx.x + threadIdx.x+1];
    }

    __syncthreads();

    fn[blockDim.x * blockIdx.x + threadIdx.x] =
        c0*(fs[threadIdx.x] + fs[threadIdx.x + 2]) + c1*fs[threadIdx.x + 1];
}

void diffusion1dQuestion(float *f, float *fn, int n, float c0, float c1)
{
    declare_precondition(
        "n == blockDim.x * gridDim.x",
        "n > 1"
        );
    declare_postcondition(
        "fn[0] == c0 * (f[0] + f[1]) + c1 * f[0]",
        "fn[n - 1] == c0 * (f[n - 2] + f[n - 1]) + c1 * f[n - 1]",
        "forall j. 0 < j -> j < n - 1 ->
            fn[j] == c0 * (f[j - 1] + f[j + 1]) + c1 * f[j]"
        );

    int j, js = threadIdx.x + 1;
    /* float fcc, fce, fcw; */
    __attribute__((shared)) float fs[];
    
    j = blockDim.x * blockIdx.x + threadIdx.x;
    fs[js] = f[j];

    if(threadIdx.x == 0) {
        fs[0] = (blockIdx.x == 0) ?fs[1] : f[j-1];
    }
    if(threadIdx.x == blockDim.x - 1) {
        fs[js + 1] = (blockIdx.x == gridDim.x - 1) ? fs[js] : f[j+1];
    }

    __syncthreads();

    /* fcc = fs[js]; */
    /* fcw = fs[js - 1]; */
    /* fce = fs[js + 1]; */
    /* fn[j] = c0 * (fcw + fce) + c1 * fcc; */

    fn[j] = c0*(fs[js - 1] + fs[js + 1]) + c1*fs[js];
}

void diffusion1dDirectional(float *f, float *fn, int n, float c0, float c1)
{
  declare_precondition(
    "n == blockDim.x * gridDim.x",
    "n > 1"
  );
  declare_postcondition(
    "fn[n - 1] == (c0 + c1) * f[n - 1]",
    "forall j. j >= 0 -> j < n - 1 ->
      fn[j] == c0 * f[j + 1] + c1 * f[j]"
  );

  int j, js = threadIdx.x;
  __attribute__((shared)) float fs[];

  j = blockDim.x * blockIdx.x + threadIdx.x;
  fs[js] = f[j];

  if(threadIdx.x == blockDim.x - 1) {
    fs[js + 1] = blockIdx.x == gridDim.x - 1 ? fs[js] : f[j+1];
  }

  __syncthreads();

  fn[j] = c0 * fs[js + 1] + c1 * fs[js];
}
