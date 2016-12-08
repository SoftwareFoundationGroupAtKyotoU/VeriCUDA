__global__ void scp(int *a, int *b, int gsize) {
  /*@ requires gsize == blockDim.x;
      ensures \forall i; 0 <= i && i < gsize -> b[i] == (i+1) % gsize; */
  int tid = threadIdx.x;
  a[tid] = tid;
  __syncthreads();
  b[tid] = a[(tid+1) % gsize];
}
