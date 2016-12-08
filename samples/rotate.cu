__global__ void rotate(int *a, int size) {
  /*@ ghost int a0[];
      requires size == blockDim.x;
      requires \forall i; a[i] == a0[i];
      ensures \forall i; 0 < i && i < size - 1 -> a[i] == a0[i - 1];
      ensures a[0] == a0[size - 1] */
  int tmp = a[threadIdx.x];
  int t = threadIdx.x + 1;
  if (t == size) t = 0;
  __syncthreads();
  a[t] = tmp;
}
