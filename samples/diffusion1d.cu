/* These programs are based on the code available from
   http://www.kohgakusha.co.jp/support/cuda/
*/

#define blockDim_x 256
#define blockDim_y   8

__global__ void diffusion1d_naive (
   float    *f,         /* dependent variable                        */
   float    *fn,        /* dependent variable                        */
   int      n,          /* grid number in the x-direction            */
   float    c0,         /* coefficient no.0                          */
   float    c1          /* coefficient no.1                          */)
{
  /*@ requires n == blockDim.x * gridDim.x;
      requires n > 1
      ensures fn[0] == c0 * (f[0] + f[1]) + c1 * f[0];
      ensures fn[n - 1] == c0 * (f[n - 2] + f[n - 1]) + c1 * f[n - 1];
      ensures \forall j; 0 < j -> j < n - 1 ->
        fn[j] == c0 * (f[j - 1] + f[j + 1]) + c1 * f[j]; */

  int   j;
  float fcc, fce, fcw;

  j = blockDim.x*blockIdx.x + threadIdx.x;

  fcc = f[j];

  if (j == 0) fcw = fcc;
  else        fcw = f[j - 1];

  if (j == n - 1) fce = fcc;
  else            fce = f[j+1];

  fn[j] = c0*(fcw + fce) + c1*fcc;
}

__global__ void diffusion1d(float *f, float *fn, int n, float c0, float c1) {
  /*@ requires n == blockDim.x * gridDim.x;
      requires n > 1;
      ensures fn[0] == c0 * (f[0] + f[1]) + c1 * f[0];
      ensures fn[n - 1] == c0 * (f[n - 2] + f[n - 1]) + c1 * f[n - 1];
      ensures \forall j; 0 < j -> j < n - 1 ->
        fn[j] == c0 * (f[j - 1] + f[j + 1]) + c1 * f[j]; */

  int j, js = threadIdx.x + 1;
  __shared__ float fs[];

  j = blockDim.x * blockIdx.x + threadIdx.x;
  fs[js] = f[j];

  if (threadIdx.x == 0) {
    fs[0] = (blockIdx.x == 0) ?fs[1] : f[j-1];
  }
  if (threadIdx.x == blockDim.x - 1) {
    fs[js + 1] = (blockIdx.x == gridDim.x - 1) ? fs[js] : f[j+1];
  }

  __syncthreads();

  fn[j] = c0*(fs[js - 1] + fs[js + 1]) + c1*fs[js];
}
