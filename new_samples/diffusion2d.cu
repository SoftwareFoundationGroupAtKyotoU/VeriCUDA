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
void  diffusion2d_naive
// ====================================================================
//
// program    :  CUDA device code for 2-D diffusion equation
//               for 16 x 16 block and 16 x 16 thread per 1 block
//
// date       :  Nov 07, 2008
// programmer :  Takayuki Aoki
// place      :  Tokyo Institute of Technology
//
(
   float    *f,         /* dependent variable                        */
   float    *fn,        /* dependent variable                        */
   int      nx,         /* grid number in the x-direction            */
   int      ny,         /* grid number in the x-direction            */
   float    c0,         /* coefficient no.0                          */
   float    c1,         /* coefficient no.1                          */
   float    c2          /* coefficient no.2                          */
)
// --------------------------------------------------------------------
{
    declare_precondition(
        "nx == blockDim.x * gridDim.x",
        "ny == blockDim.y * gridDim.y",
        "nx > 1",
        "ny > 1"
        );
    declare_postcondition(
        "fn[0] == c0 * (f[0] + f[1]) + c1 * (f[0] + f[nx]) + c2 * f[0]",
        "fn[nx - 1] ==
            c0 * (f[nx - 2] + f[nx - 1]) +
            c1 * (f[nx - 1] + f[2 * nx - 1]) +
            c2 * f[nx - 1]",
        "fn[nx * (ny - 1)] ==
            c0 * (f[nx * (ny - 1)] + f[nx * (ny - 1) + 1]) +
            c1 * (f[nx * (ny - 2)] + f[nx * (ny - 1)]) +
            c2 * f[nx * (ny - 1)]",
        "fn[nx * (ny - 1) + nx - 1] ==
            c0 * (f[nx * (ny - 1) + nx - 2] + f[nx * (ny - 1) + nx - 1]) +
            c1 * (f[nx * (ny - 2) + nx - 1] + f[nx * (ny - 1) + nx - 1]) +
            c2 * f[nx * (ny - 1) + nx - 1]",
        "forall jy. 0 < jy -> jy < ny - 1 ->
             fn[nx * jy] ==
                 c0 * (f[nx * jy] + f[nx * jy + 1]) +
                 c1 * (f[nx * (jy - 1)] + f[nx * (jy + 1)]) +
                 c2 * f[nx * jy]",
        "forall jy. 0 < jy -> jy < ny - 1 ->
             fn[nx * jy + nx - 1] ==
                 c0 * (f[nx * jy + nx - 2] + f[nx * jy + nx - 1]) +
                 c1 * (f[nx * (jy - 1) + nx - 1] + f[nx * (jy + 1) + nx - 1]) +
                 c2 * f[nx * jy + nx - 1]",
        "forall jx. 0 < jx -> jx < nx - 1 ->
             fn[jx] ==
                 c0 * (f[jx - 1] + f[jx + 1]) +
                 c1 * (f[jx] + f[nx + jx]) +
                 c2 * f[jx]",
        "forall jx. 0 < jx -> jx < nx - 1 ->
             fn[nx * (ny - 1) + jx] ==
                 c0 * (f[nx * (ny - 1) + jx - 1] + f[nx * (ny - 1) + jx + 1]) +
                 c1 * (f[nx * (ny - 2) + jx] + f[nx * (ny - 1) + jx]) +
                 c2 * f[nx * (ny - 1) + jx]",
        "forall jx. 0 < jx -> jx < nx - 1 ->
            forall jy. 0 < jy -> jy < ny - 1 ->
                fn[nx * jy + jx] ==
                    c0 * (f[nx * jy + jx - 1] + f[nx * jy + jx + 1]) +
                    c1 * (f[nx * (jy - 1) + jx] + f[nx * (jy + 1) + jx]) +
                    c2 * f[nx * jy + jx]"
        );

   int    j,    jx,   jy;
   float  fcc,  fce,  fcw,  fcs,  fcn;

   jy = blockDim.y*blockIdx.y + threadIdx.y;
   jx = blockDim.x*blockIdx.x + threadIdx.x;
   j = nx*jy + jx;

   fcc = f[j];

   if(jx == 0) fcw = fcc;
   else        fcw = f[j - 1];

   if(jx == nx - 1) fce = fcc;
   else             fce = f[j+1];

   if(jy == 0) fcs = fcc;
   else        fcs = f[j-nx];

   if(jy == ny - 1) fcn = fcc;
   else             fcn = f[j+nx];

   fn[j] = c0*(fcw + fce)
         + c1*(fcs + fcn)
         + c2*fcc;
}
