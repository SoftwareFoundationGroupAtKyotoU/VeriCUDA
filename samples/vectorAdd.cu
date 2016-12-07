__global__ void
vectorAdd1(const float *A, const float *B, float *C, int numElements) {
  /*@ requires 0 <= numElements;
      requires numElements < gridDim.x * blockDim.x;
      ensures  forall i. 0 <= i -> i < numElements -> C[i] == A[i] + B[i]; */
  int i = blockDim.x * blockIdx.x + threadIdx.x;
  if (i < numElements) {
    C[i] = A[i] + B[i];
  }
}

__global__ void
vectorAdd(const float *A, const float *B, float *C, int numElements) {
  /*@ ghost int m;
      requires numElements == m * blockDim.x * gridDim.x;
      ensures forall i [C[i]]. 0 <= i -> i < numElements -> C[i] == A[i] + B[i]; */

  int i = blockDim.x * blockIdx.x + threadIdx.x;

  /*@ loop invariant
        (exists t : thread. active(t)) -> forall t : thread. active(t);
      loop invariant
        i == loop_count * blockDim.x * gridDim.x + blockDim.x * blockIdx.x + threadIdx.x;
      loop invariant forall k [C[k]].
        0 <= k && k < blockDim.x * gridDim.x * loop_count -> C[k] == A[k] + B[k]; */
  while (i < numElements) {
    C[i] = A[i] + B[i];
    i += gridDim.x * blockDim.x;
  }
}

__global__ void
vectorAdd_non_unif(const float *A, const float *B, float *C, int numElements) {
  /*@ requires numElements > 0;
      ensures forall i. 0 <= i -> i < numElements -> C[i] == A[i] + B[i] */

  int i = blockDim.x * blockIdx.x + threadIdx.x;

  /*@ loop invariant
        (loop_count - 1) * blockDim.x * gridDim.x +
          blockDim.x * blockIdx.x + threadIdx.x < numElements ->
        i == loop_count * blockDim.x * gridDim.x + blockDim.x * blockIdx.x + threadIdx.x;
      loop invariant
        (loop_count - 1) * blockDim.x * gridDim.x +
          blockDim.x * blockIdx.x + threadIdx.x >= numElements ->
        i == (loop_count - 1) * blockDim.x * gridDim.x +
          blockDim.x * blockIdx.x + threadIdx.x;
      loop invariant forall k.
        0 <= k && k < blockDim.x * gridDim.x * loop_count && k < numElements ->
        C[k] == A[k] + B[k]; */
  while (i < numElements) {
    C[i] = A[i] + B[i];
    i += gridDim.x * blockDim.x;
  }
}

__global__ void
vectorAddDownward(const float *A, const float *B, float *C, int numElements) {
  /*@ ghost int m
      requires numElements == m * blockDim.x * gridDim.x;
      ensures forall i [C[i]]. 0 <= i -> i < numElements -> C[i] == A[i] + B[i]; */

  int i = numElements - 1 - blockDim.x * blockIdx.x - threadIdx.x;

  /*@ loop invariant
        (exists t : thread. active(t)) -> forall t : thread. active(t);
      loop invariant
        i == numElements - 1 - loop_count * blockDim.x * gridDim.x -
        blockDim.x * blockIdx.x - threadIdx.x;
      loop invariant forall k [C[k]].
        numElements - blockDim.x * gridDim.x * loop_count <= k && k < numElements ->
        C[k] == A[k] + B[k]; */
  while (0 <= i) {
    C[i] = A[i] + B[i];
    i -= gridDim.x * blockDim.x;
  }
}
