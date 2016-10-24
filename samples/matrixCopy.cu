// taken from NVIDIA_CUDA-6.5_Samples/6_Advanced/transpose/transpose.cu

// Each block transposes/copies a tile of TILE_DIM x TILE_DIM elements
// using TILE_DIM x BLOCK_ROWS threads, so that each thread transposes
// TILE_DIM/BLOCK_ROWS elements.  TILE_DIM must be an integral multiple of BLOCK_ROWS

/* #define TILE_DIM    16 */
/* #define BLOCK_ROWS  16 */

struct __attribute__((device_builtin)) uint3
{
    unsigned int x, y, z;
};
typedef __attribute__((device_builtin)) struct uint3 uint3;

struct __attribute__((device_builtin)) dim3
{
    unsigned int x, y, z;
};
typedef __attribute__((device_builtin)) struct dim3 dim3;

uint3 __attribute__((device_builtin)) extern const threadIdx;
uint3 __attribute__((device_builtin)) extern const blockIdx;
dim3 __attribute__((device_builtin)) extern const blockDim;
dim3 __attribute__((device_builtin)) extern const gridDim;
int __attribute__((device_builtin)) extern const warpSize;

extern __attribute__((device)) __attribute__((device_builtin)) void __syncthreads(void);

// -------------------------------------------------------
// Copies
// width and height must be integral multiples of TILE_DIM
// -------------------------------------------------------

void copySingle(float *odata, float *idata, int width, int height, int TILE_DIM)
{
    declare_precondition(
        "blockDim.x == TILE_DIM",
        "blockDim.y == TILE_DIM",
        "width == blockDim.x * gridDim.x",
        "height == blockDim.y * gridDim.y"
        );
    declare_postcondition(
        "forall i. 0 <= i && i < width * height -> odata[i] == idata[i]"
        );
    int xIndex = blockIdx.x * TILE_DIM + threadIdx.x;
    int yIndex = blockIdx.y * TILE_DIM + threadIdx.y;

    int index  = xIndex + width * yIndex;

    odata[index] = idata[index];
}

void copySingleSharedMem(float *odata, float *idata, int width, int height,
                         int TILE_DIM)
{
    declare_precondition(
        "blockDim.x == TILE_DIM",
        "blockDim.y == TILE_DIM",
        "width == blockDim.x * gridDim.x",
        "height == blockDim.y * gridDim.y"
        );
    declare_postcondition(
        "forall i. 0 <= i && i < width * height -> odata[i] == idata[i]"
        );

    __attribute__((shared)) float tile[][];

    int xIndex = blockIdx.x * TILE_DIM + threadIdx.x;
    int yIndex = blockIdx.y * TILE_DIM + threadIdx.y;

    int index  = xIndex + width*yIndex;

    tile[threadIdx.y][threadIdx.x] = idata[index];

    __syncthreads();

    odata[index] = tile[threadIdx.y][threadIdx.x];
}

void copy(float *odata, float *idata, int width, int height,
          int TILE_DIM, int BLOCK_ROWS)
{
    declare_logic_param("int m");
    declare_precondition(
        "0 < m",
        "0 < BLOCK_ROWS",
        "TILE_DIM == m * BLOCK_ROWS",
        "blockDim.x == TILE_DIM",
        "blockDim.y == BLOCK_ROWS",
        "width == TILE_DIM * gridDim.x",
        "height == TILE_DIM * gridDim.y"
        );
    declare_postcondition(
        "forall i. 0 <= i && i < width * height -> odata[i] == idata[i]"
        );
    int xIndex = blockIdx.x * TILE_DIM + threadIdx.x;
    int yIndex = blockIdx.y * TILE_DIM + threadIdx.y;

    int index  = xIndex + width*yIndex;

    for (int i=0; i<TILE_DIM; i+=BLOCK_ROWS)
    {
        declare_invariant(
            "i == BLOCK_ROWS * loop_count",
            "loop_count <= m",
            "forall j. 0 <= j && j < loop_count ->
                odata[index + j * BLOCK_ROWS * width] ==
                idata[index + j * BLOCK_ROWS * width]"
            );
        odata[index+i*width] = idata[index+i*width];
    }
}

void copySharedMem(float *odata, float *idata, int width, int height,
                   int TILE_DIM, int BLOCK_ROWS)
{
    declare_logic_param("int m");
    declare_precondition(
        "0 <= m",
        "TILE_DIM == m * BLOCK_ROWS",
        "blockDim.x == TILE_DIM",
        "blockDim.y == BLOCK_ROWS",
        "width == TILE_DIM * gridDim.x",
        "height == TILE_DIM * gridDim.y"
        );
    declare_postcondition(
        "forall i. 0 <= i && i < width * height -> odata[i] == idata[i]"
        );

    __attribute__((shared)) float tile[][];

    int xIndex = blockIdx.x * TILE_DIM + threadIdx.x;
    int yIndex = blockIdx.y * TILE_DIM + threadIdx.y;

    int index  = xIndex + width*yIndex;

    for (int i=0; i<TILE_DIM; i+=BLOCK_ROWS)
    {
        declare_invariant(
            "i == BLOCK_ROWS * loop_count",
            "loop_count <= m",
            "forall j. 0 <= j && j < i ->
               tile[threadIdx.y + j][threadIdx.x] == idata[index + j * width]"
            );
        tile[threadIdx.y + i][threadIdx.x] = idata[index + i * width];
    }

    assert("forall x. 0 <= x && x < width -> forall y. 0 <= y && y < height ->
               tile[y][x] == idata[x + y * width]");
    __syncthreads();

    for (int i=0; i<TILE_DIM; i+=BLOCK_ROWS)
    {
        declare_invariant(
            "i == BLOCK_ROWS * loop_count",
            "loop_count <= m",
            "forall j. 0 <= j && j < i ->
               odata[index + j * width] == tile[threadIdx.y + j][threadIdx.x]"
            );
        odata[index + i * width] = tile[threadIdx.y + i][threadIdx.x];
    }
}

