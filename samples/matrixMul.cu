/* These programs are based on NVIDIA's sample program
   NVIDIA_CUDA-6.5_Samples/0_Simple/matrixMul/matrixMul.cu
 */

__global__ void matrixMulCUDA(float *C, float *A, float *B, int wA, int wB) {
  /*@ ghost int m;
      ghost int hA;
      requires blockDim.x == 16;
      requires blockDim.y == 16;
      requires 0 <= m;
      requires wA == 16 * m;
      requires wB == gridDim.x * 16;
      requires hA == gridDim.y * 16;
      ensures \forall i; \forall j;
        0 <= i && i < hA && 0 <= j && j < wB ->
        C[wB * i + j] == \sum(0, wA-1,
                \lambda integer k; A[wA * i + k] * B[wB * k + j]); */

  int bx = blockIdx.x;
  int by = blockIdx.y;
  int tx = threadIdx.x;
  int ty = threadIdx.y;
  int aBegin = wA * 16 * by;
  int aEnd = aBegin + wA - 1;
  int aStep = 16;
  int bBegin = 16 * bx;
  int bStep = 16 * wB;
  float Csub = 0;

  /*@ loop invariant loop_count <= m;
      loop invariant a == aBegin + aStep * loop_count;
      loop invariant b == bBegin + bStep * loop_count;
      loop invariant \forall t : thread;
        Csub@t == \sum(0, 16 * loop_count - 1,
                \lambda integer k; A[wA * (16 * by@t + ty@t) + k] * B[wB * k + 16 * bx@t + tx@t]); */
  for (int a = aBegin, b = bBegin; a <= aEnd; a += aStep, b += bStep) {
    __shared__ float As[16][16];
    __shared__ float Bs[16][16];

    As[ty][tx] = A[a + wA * ty + tx];
    Bs[ty][tx] = B[b + wB * ty + tx];
    __syncthreads();

#pragma unroll
    /*@ loop invariant k == loop_count;
        loop invariant loop_count <= 16;
        loop invariant \forall t : thread; Csub@t ==
          \sum(0, 16 * loop_count_2 + loop_count - 1,
                \lambda integer k; A[wA * (16 * by@t + ty@t) + k] * B[wB * k + 16 * bx@t + tx@t]); */
    for (int k = 0; k < 16; ++k) {
      Csub += As[ty][k] * Bs[k][tx];
    }
    __syncthreads();
  }
  int c = wB * 16 * by + 16 * bx;
  C[c + wB * ty + tx] = Csub;
}

__global__ void matrixMul(float *C, float *A, float *B, int wA, int wB, int bsize) {
  /*@ ghost int m, hA;
      requires blockDim.x == bsize;
      requires blockDim.y == bsize;
      requires 0 <= m;
      requires wA == bsize * m;
      requires wB == gridDim.x * bsize;
      requires hA == gridDim.y * bsize; */
  /*  ensures \forall i1; \forall i2; \forall j1; \forall j2;
        0 <= i1 && i1 < gridDim.y && 0 <= i2 && i2 < bsize &&
        0 <= j1 && j1 < gridDim.x && 0 <= j2 && j2 < bsize ->
          C[wB * (i1 * bsize + i2) + (j1 * bsize + j2)] ==
          \sum(0, wA-1, \lambda integer k; A[wA * (i1 * bsize + i2) + k] * B[wB * k + j1 * bsize + j2]); */
  /* The experiment reported in the new version of the paper uses
     the above postcondition, but the current implementation can
     verify the following, more natural one. */
  /*@ ensures \forall i; \forall j;
        0 <= i && i < hA && 0 <= j && j < wB ->
          C[wB * i + j] == \sum(0, wA-1, \lambda integer k; A[wA * i + k] * B[wB * k + j]); */
  int bx = blockIdx.x;
  int by = blockIdx.y;
  int tx = threadIdx.x;
  int ty = threadIdx.y;
  int aBegin = wA * bsize * by;
  int aEnd = aBegin + wA - 1;
  int aStep = bsize;
  int bBegin = bsize * bx;
  int bStep = bsize * wB;
  float Csub = 0;
  /*@ loop invariant loop_count <= m;
      loop invariant a == aBegin + aStep * loop_count;
      loop invariant b == bBegin + bStep * loop_count;
      loop invariant Csub ==
        \sum(0, bsize * loop_count - 1,
             \lambda integer k; A[wA * (bsize * by + ty) + k] * B[wB * k + bsize * bx + tx]); */
  for (int a = aBegin, b = bBegin; a <= aEnd; a += aStep, b += bStep) {
    __shared__ float As[][], Bs[][];
    As[ty][tx] = A[a + wA * ty + tx];
    Bs[ty][tx] = B[b + wB * ty + tx];
    __syncthreads();
  /*@ loop invariant k == loop_count;
      loop invariant loop_count <= bsize;
      loop invariant Csub ==
        \sum(0, bsize * loop_count_2 + loop_count - 1,
             \lambda integer k; A[wA * (bsize * by + ty) + k] * B[wB * k + bsize * bx + tx]); */    
    for (int k = 0; k < bsize; ++k) {
      Csub += As[ty][k] * Bs[k][tx];
    }
    __syncthreads();
  }
  int c = wB * bsize * by + bsize * bx;
  C[c + wB * ty + tx] = Csub;
}

__global__ int bsize_x;
__global__ int bsize_y;

void matrixMul2(float *C, float *A, float *B, int wA, int wB) {
  /*@ ghost int m, hA;
      requires 0 < bsize_x;
      requires bsize_x == 2 * bsize_y;
      requires blockDim.x == bsize_x;
      requires blockDim.y == bsize_y;
      requires 0 <= m;
      requires wA == bsize_x * m;
      requires wB == gridDim.x * bsize_x;
      requires hA == gridDim.y * bsize_x;
      ensures \forall i1; \forall i2; \forall j1; \forall j2;
        0 <= i1 && i1 < gridDim.y && 0 <= i2 && i2 < 2 * bsize_y &&
        0 <= j1 && j1 < gridDim.x && 0 <= j2 && j2 < 2 * bsize_y ->
          C[wB * (i1 * 2 * bsize_y + i2) + j1 * 2 * bsize_y + j2] ==
            \sum(0, wA-1, \lambda integer k;
                            A[wA * (i1 * 2 * bsize_y + i2) + k] *
                            B[wB * k + j1 * 2 * bsize_y + j2]); */
  int bx = blockIdx.x;
  int by = blockIdx.y;
  int tx = threadIdx.x;
  int ty = threadIdx.y;
  int aBegin = wA * bsize_x * by;
  int aEnd = aBegin + wA - 1;
  int aStep = bsize_x;
  int bBegin = bsize_x * bx;
  int bStep = bsize_x * wB;
  float Csub[] = {0, 0};

  /*@ loop invariant loop_count <= m;
      loop invariant a == aBegin + aStep * loop_count;
      loop invariant b == bBegin + bStep * loop_count;
      loop invariant Csub[0] ==
        \sum(0, bsize_x * loop_count - 1,
             \lambda integer k; A[wA * (bsize_x * by + ty) + k] * B[wB * k + bsize_x * bx + tx]);
      loop invariant Csub[1] ==
        \sum(0, bsize_x * loop_count - 1,
             \lambda integer k; A[wA * (bsize_x * by + (ty + bsize_y)) + k] * B[wB * k + bsize_x * bx + tx]); */
  for (int a = aBegin, b = bBegin; a <= aEnd; a += aStep, b += bStep) {
    __shared__ float As[][];
    __shared__ float Bs[][];

    As[ty][tx] = A[a + wA * ty + tx];
    Bs[ty][tx] = B[b + wB * ty + tx];
    As[ty + bsize_y][tx] = A[a + wA * (ty + bsize_y) + tx];
    Bs[ty + bsize_y][tx] = B[b + wB * (ty + bsize_y) + tx];
    __syncthreads();

    /*@ loop invariant k == loop_count;
        loop invariant loop_count <= bsize_x;
        loop invariant Csub[0] ==
          \sum(0, bsize_x * loop_count_2 + loop_count - 1,
               \lambda integer k; A[wA * (bsize_x * by + ty) + k] * B[wB * k + bsize_x * bx + tx]);
        loop invariant Csub[1] ==
          \sum(0, bsize_x * loop_count_2 + loop_count - 1,
               \lambda integer k; A[wA * (bsize_x * by + ty + bsize_y) + k] * B[wB * k + bsize_x * bx + tx]); */
    for (int k = 0; k < bsize_x; ++k) {
      Csub[0] += As[ty][k] * Bs[k][tx];
      Csub[1] += As[ty + bsize_y][k] * Bs[k][tx];
    }
    __syncthreads();
  }

  int c = wB * bsize_x * by + bsize_x * bx;
  C[c + wB * ty + tx] = Csub[0];
  C[c + wB * (ty + bsize_y) + tx] = Csub[1];
}

void matrixMul4(float *C, float *A, float *B, int wA, int wB) {
  /*@ ghost int m, hA
      requires 0 < bsize_x;
      requires bsize_x == 4 * bsize_y;
      requires blockDim.x == bsize_x;
      requires blockDim.y == bsize_y;
      requires 0 <= m;
      requires wA == bsize_x * m;
      requires wB == gridDim.x * bsize_x;
      requires hA == gridDim.y * bsize_x;
      ensures \forall i1; \forall i2; \forall j1; \forall j2;
        0 <= i1 && i1 < gridDim.y && 0 <= i2 && i2 < 4 * bsize_y &&
        0 <= j1 && j1 < gridDim.x && 0 <= j2 && j2 < 4 * bsize_y ->
          C[wB * (i1 * 4 * bsize_y + i2) + j1 * 4 * bsize_y + j2] ==
          \sum(0, wA-1, \lambda integer k;
                          A[wA * (i1 * 4 * bsize_y + i2) + k] *
                          B[wB * k + j1 * 4 * bsize_y + j2]); */
  int bx = blockIdx.x;
  int by = blockIdx.y;
  int tx = threadIdx.x;
  int ty = threadIdx.y;
  int aBegin = wA * bsize_x * by;
  int aEnd = aBegin + wA - 1;
  int aStep = bsize_x;
  int bBegin = bsize_x * bx;
  int bStep = bsize_x * wB;
  float Csub[] = {0, 0, 0, 0};

  /*@ loop invariant loop_count <= m;
      loop invariant a == aBegin + aStep * loop_count;
      loop invariant b == bBegin + bStep * loop_count;
      loop invariant Csub[0] ==
        \sum(0, bsize_x * loop_count - 1,
             \lambda integer k; A[wA * (bsize_x * by + ty) + k] * B[wB * k + bsize_x * bx + tx]);
      loop invariant Csub[1] ==
        \sum(0, bsize_x * loop_count - 1,
             \lambda integer k; A[wA * (bsize_x * by + (ty + bsize_y)) + k] *
               B[wB * k + bsize_x * bx + tx]);
      loop invariant Csub[2] ==
        \sum(0, bsize_x * loop_count - 1,
             \lambda integer k; A[wA * (bsize_x * by + (ty + 2 * bsize_y)) + k] *
             B[wB * k + bsize_x * bx + tx]);
      loop invariant Csub[3] ==
        \sum(0, bsize_x * loop_count - 1,
             \lambda integer k; A[wA * (bsize_x * by + (ty + 3 * bsize_y)) + k] *
             B[wB * k + bsize_x * bx + tx]); */
  for (int a = aBegin, b = bBegin; a <= aEnd; a += aStep, b += bStep) {
    __shared__ float As[][];
    __shared__ float Bs[][];

    As[ty][tx] = A[a + wA * ty + tx];
    Bs[ty][tx] = B[b + wB * ty + tx];
    As[ty + bsize_y][tx] = A[a + wA * (ty + bsize_y) + tx];
    Bs[ty + bsize_y][tx] = B[b + wB * (ty + bsize_y) + tx];
    As[ty + 2 * bsize_y][tx] = A[a + wA * (ty + 2 * bsize_y) + tx];
    Bs[ty + 2 * bsize_y][tx] = B[b + wB * (ty + 2 * bsize_y) + tx];
    As[ty + 3 * bsize_y][tx] = A[a + wA * (ty + 3 * bsize_y) + tx];
    Bs[ty + 3 * bsize_y][tx] = B[b + wB * (ty + 3 * bsize_y) + tx];
    __syncthreads();

    /*@ loop invariant k == loop_count;
        loop invariant loop_count <= bsize_x;
        loop invariant Csub[0] ==
          \sum(0, bsize_x * loop_count_2 + loop_count - 1,
               \lambda integer k; A[wA * (bsize_x * by + ty) + k] * B[wB * k + bsize_x * bx + tx]);
        loop invariant Csub[1] ==
          \sum(0, bsize_x * loop_count_2 + loop_count - 1,
               \lambda integer k; A[wA * (bsize_x * by + ty + bsize_y) + k] * B[wB * k + bsize_x * bx + tx]);
        loop invariant Csub[2] ==
          \sum(0, bsize_x * loop_count_2 + loop_count - 1,
               \lambda integer k; A[wA * (bsize_x * by + ty + 2 * bsize_y) + k] * B[wB * k + bsize_x * bx + tx]);
        loop invariant Csub[3] ==
          \sum(0, bsize_x * loop_count_2 + loop_count - 1,
               \lambda integer k; A[wA * (bsize_x * by + ty + 3 * bsize_y) + k] * B[wB * k + bsize_x * bx + tx]); */
    for (int k = 0; k < bsize_x; ++k) {
      Csub[0] += As[ty][k] * Bs[k][tx];
      Csub[1] += As[ty + bsize_y][k] * Bs[k][tx];
      Csub[2] += As[ty + 2 * bsize_y][k] * Bs[k][tx];
      Csub[3] += As[ty + 3 * bsize_y][k] * Bs[k][tx];
    }
    __syncthreads();
  }
  int c = wB * bsize_x * by + bsize_x * bx;
  C[c + wB * ty + tx] = Csub[0];
  C[c + wB * (ty + bsize_y) + tx] = Csub[1];
  C[c + wB * (ty + 2 * bsize_y) + tx] = Csub[2];
  C[c + wB * (ty + 3 * bsize_y) + tx] = Csub[3];
}

void matrixMulk(float *C, float *A, float *B, int wA, int wB, int k) {
  /*@ ghost int m, hA, i0, j0;
      ghost real dummy;
      requires 0 < bsize_y;
      requires 0 < k;
      requires bsize_x == k * bsize_y;
      requires blockDim.x == bsize_x;
      requires blockDim.y == bsize_y;
      requires 0 <= m;
      requires wA == bsize_x * m;
      requires wB == gridDim.x * bsize_x;
      requires hA == gridDim.y * bsize_x;
      requires C[wB * i0 + j0] == dummy;
      ensures C[wB * i0 + j0] == \sum(0, wA-1, \lambda integer k; A[wA * i0 + k] * B[wB * k + j0]); */
  int bx = blockIdx.x;
  int by = blockIdx.y;
  int tx = threadIdx.x;
  int ty = threadIdx.y;
  int aBegin = wA * bsize_x * by;
  int aEnd = aBegin + wA - 1;
  int aStep = bsize_x;
  int bBegin = bsize_x * bx;
  int bStep = bsize_x * wB;
  float Csub[];

  /*@ loop invariant i1 == loop_count;
      loop invariant loop_count <= k;
      loop invariant \forall i; 0 <= i && i < i1 -> Csub[i] == 0; */
  for (int i1 = 0; i1 < k; i1++) {
    Csub[i1] = 0;
  }

  /*@ loop invariant loop_count <= m;
      loop invariant a == aBegin + aStep * loop_count;
      loop invariant b == bBegin + bStep * loop_count;
      loop invariant \forall i; 0 <= i && i < k ->
        Csub[i] == \sum(0, bsize_x * loop_count - 1,
                        \lambda integer k; A[wA * (bsize_x * by + ty + bsize_y * i) + k] *
                          B[wB * k + bsize_x * bx + tx]); */
  for (int a = aBegin, b = bBegin; a <= aEnd; a += aStep, b += bStep) {
    __shared__ float As[][];
    __shared__ float Bs[][];
    /*@ loop invariant i0 == loop_count;
        loop invariant loop_count <= k;
        loop invariant \forall i; 0 <= i && i < loop_count ->
          As[ty + bsize_y * i][tx] == A[a + wA * (ty + bsize_y * i) + tx];
        loop invariant \forall i; 0 <= i && i < loop_count ->
          Bs[ty + bsize_y * i][tx] == B[b + wB * (ty + bsize_y * i) + tx]; */
    for (int i0 = 0; i0 < k; i0++) {
      As[ty + bsize_y * i0][tx] = A[a + wA * (ty + bsize_y * i0) + tx];
      Bs[ty + bsize_y * i0][tx] = B[b + wB * (ty + bsize_y * i0) + tx];
    }
    __syncthreads();

    /*@ loop invariant l == loop_count;
        loop invariant loop_count <= bsize_x;
        loop invariant \forall i; 0 <= i && i < k ->
          Csub[i] == \sum(0, bsize_x * loop_count_2 + loop_count - 1,
                          \lambda integer k;
                            A[wA * (bsize_x * by + ty + bsize_y * i) + k] *
                            B[wB * k + bsize_x * bx + tx]); */
    for (int l = 0; l < bsize_x; ++l) {
      /*@ loop invariant i == loop_count;
          loop invariant loop_count <= k;
          loop invariant \forall j; 0 <= j && j < loop_count ->
            Csub[j] == \sum(0, bsize_x * loop_count_3 + loop_count_2,
                            \lambda integer k;
                              A[wA * (bsize_x * by + ty + bsize_y * j) + k] *
                              B[wB * k + bsize_x * bx + tx]);
          loop invariant \forall j; loop_count <= j && j < k ->
            Csub[j] == \sum(0, bsize_x * loop_count_3 + loop_count_2 - 1,
                            \lambda integer k;
                              A[wA * (bsize_x * by + ty + bsize_y * j) + k] *
                              B[wB * k + bsize_x * bx + tx]); */
      for (int i = 0; i < k; i++) {
        Csub[i] += As[ty + bsize_y * i][l] * Bs[l][tx];
      }
    }
    __syncthreads();
  }

  int c = wB * bsize_x * by + bsize_x * bx;
  /*@ loop invariant j == loop_count;
      loop invariant loop_count <= k;
      loop invariant \forall j; 0 <= j && j < loop_count ->
      C[c + wB * (ty + bsize_y * j) + tx] == Csub[j]; */
  for (int j = 0; j < k; j++) {
    C[c + wB * (ty + bsize_y * j) + tx] = Csub[j];
  }
}
