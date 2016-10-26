__global__ void
arraySum_0(const int *A, const int *S, unsigned int n) {
  /*@ ghost int m;
      requires 0 < m;
      requires blockDim.x == 2 ^ m;
      requires forall i. A[i] == 1;
      ensures S[blockIdx.x] == blockDim.x; */

  __shared__ int sdata[];
  unsigned int i = blockDim.x * blockIdx.x + threadIdx.x;

  sdata[threadIdx.x] = A[i];

  __syncthreads();

  /*@ loop invariant s >= 0;
      loop invariant s > 0 -> s == 2 ^ (m - loop_count - 1);
      loop invariant 0 <= loop_count && loop_count <= m;
      loop invariant forall i.
        0 <= i && i < 2 * s -> sdata[i] == 2^loop_count; */
  for (unsigned int s = blockDim.x/2; s > 0; s /= 2) {
    if (threadIdx.x < s) sdata[threadIdx.x] += sdata[threadIdx.x + s];
    __syncthreads();
  }

  //@ assert sdata[0] == blockDim.x
  if (threadIdx.x == 0) S[blockIdx.x] = sdata[0];
}
