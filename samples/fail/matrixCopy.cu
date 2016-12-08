/* These programs are based on NVIDIA's sample program
   NVIDIA_CUDA-6.5_Samples/6_Advanced/transpose/transpose.cu
*/

__global__ void
copySingle(float *odata, float *idata, int width, int height, int TILE_DIM) {
  /*@ requires blockDim.x == TILE_DIM;
      requires blockDim.y == TILE_DIM;
      requires width == blockDim.x * gridDim.x;
      requires height == blockDim.y * gridDim.y;
      ensures \forall i; 0 <= i && i < width * height -> odata[i] == idata[i]; */

  int xIndex = blockIdx.x * TILE_DIM + threadIdx.x;
  int yIndex = blockIdx.y * TILE_DIM + threadIdx.y;
  int index  = xIndex + width * yIndex;
  odata[index] = idata[index];
}

__global__ void
copySingleSharedMem(float *odata, float *idata, int width, int height, int TILE_DIM) {
  /*@ requires blockDim.x == TILE_DIM;
      requires blockDim.y == TILE_DIM;
      requires width == blockDim.x * gridDim.x;
      requires height == blockDim.y * gridDim.y;
      ensures \forall i; 0 <= i && i < width * height -> odata[i] == idata[i]; */

  __shared__ float tile[][];
  int xIndex = blockIdx.x * TILE_DIM + threadIdx.x;
  int yIndex = blockIdx.y * TILE_DIM + threadIdx.y;
  int index  = xIndex + width*yIndex;

  tile[threadIdx.y][threadIdx.x] = idata[index];
  __syncthreads();
  odata[index] = tile[threadIdx.y][threadIdx.x];
}

__global__ void
copy(float *odata, float *idata, int width, int height, int TILE_DIM, int BLOCK_ROWS) {
  /*@ ghost int m;
      requires 0 < m;
      requires 0 < BLOCK_ROWS;
      requires TILE_DIM == m * BLOCK_ROWS;
      requires blockDim.x == TILE_DIM;
      requires blockDim.y == BLOCK_ROWS;
      requires width == TILE_DIM * gridDim.x;
      requires height == TILE_DIM * gridDim.y;
      ensures \forall i; 0 <= i && i < width * height -> odata[i] == idata[i]; */

  int xIndex = blockIdx.x * TILE_DIM + threadIdx.x;
  int yIndex = blockIdx.y * TILE_DIM + threadIdx.y;
  int index  = xIndex + width*yIndex;

  /*@ loop invariant i == BLOCK_ROWS * loop_count;
      loop invariant loop_count <= m;
      loop invariant \forall j;
        0 <= j && j < loop_count ->
        odata[index + j * BLOCK_ROWS * width] == idata[index + j * BLOCK_ROWS * width]; */
  for (int i = 0; i < TILE_DIM; i += BLOCK_ROWS) {
    odata[index+i*width] = idata[index+i*width];
  }
}

__global__ void
copySharedMem(float *odata, float *idata, int width, int height, int TILE_DIM, int BLOCK_ROWS) {
  /*@ ghost int m
      requires 0 <= m;
      requires TILE_DIM == m * BLOCK_ROWS;
      requires blockDim.x == TILE_DIM;
      requires blockDim.y == BLOCK_ROWS;
      requires width == TILE_DIM * gridDim.x;
      requires height == TILE_DIM * gridDim.y;
      ensures \forall i; 0 <= i && i < width * height -> odata[i] == idata[i] */

  __shared__ float tile[][];

  int xIndex = blockIdx.x * TILE_DIM + threadIdx.x;
  int yIndex = blockIdx.y * TILE_DIM + threadIdx.y;
  int index  = xIndex + width*yIndex;

  /*@ loop invariant i == BLOCK_ROWS * loop_count;
      loop invariant loop_count <= m;
      loop invariant \forall j;
        0 <= j && j < i -> tile[threadIdx.y + j][threadIdx.x] == idata[index + j * width]; */
  for (int i = 0; i < TILE_DIM; i += BLOCK_ROWS) {
    tile[threadIdx.y + i][threadIdx.x] = idata[index + i * width];
  }

  /*@ assert \forall x; 0 <= x && x < width -> \forall y; 0 <= y && y < height ->
        tile[y][x] == idata[x + y * width] */

  __syncthreads();

  /*@ loop invariant i == BLOCK_ROWS * loop_count;
      loop invariant loop_count <= m;
      loop invariant \forall j; 0 <= j && j < i ->
        odata[index + j * width] == tile[threadIdx.y + j][threadIdx.x]; */
  for (int i = 0; i < TILE_DIM; i += BLOCK_ROWS) {
    odata[index + i * width] = tile[threadIdx.y + i][threadIdx.x];
  }
}
