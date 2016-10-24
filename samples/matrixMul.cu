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

// extern int BLOCK_SIZE;

// static const int BLOCK_SIZE = 16;
//#define BLOCK_SIZE 32

void matrixMulCUDA(float *C, float *A, float *B, int wA, int wB)
{
    declare_logic_param(
        "int m",
        "int hA");
    declare_precondition(
        "blockDim.x == 16",
        "blockDim.y == 16",
        "0 <= m",
        "wA == 16 * m",
        "wB == gridDim.x * 16",
        "hA == gridDim.y * 16");
    declare_postcondition(
        "forall i. forall j.
                0 <= i && i < hA && 0 <= j && j < wB ->
                C[wB * i + j] == sum(k, A[wA * i + k] * B[wB * k + j], 0, wA-1)");
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

    for (int a = aBegin, b = bBegin;
         a <= aEnd;
         a += aStep, b += bStep)
    {
        declare_invariant(
            "loop_count <= m",
            "a == aBegin + aStep * loop_count",
            "b == bBegin + bStep * loop_count",
            "forall t : thread. Csub@t ==
                sum(k, A[wA * (16 * by@t + ty@t) + k] * B[wB * k + 16 * bx@t + tx@t],
                    0, 16 * loop_count - 1)");
        __attribute__((shared)) float As[16][16];
        __attribute__((shared)) float Bs[16][16];

        As[ty][tx] = A[a + wA * ty + tx];
        Bs[ty][tx] = B[b + wB * ty + tx];
        __syncthreads();

#pragma unroll
        for (int k = 0; k < 16; ++k)
        {
            declare_invariant(
                "k == loop_count",
                "loop_count <= 16",
                "forall t : thread. Csub@t ==
                sum(k, A[wA * (16 * by@t + ty@t) + k] * B[wB * k + 16 * bx@t + tx@t],
                    0, 16 * loop_count_2 + loop_count - 1)");
            Csub += As[ty][k] * Bs[k][tx];
        }

        __syncthreads();
    }

    int c = wB * 16 * by + 16 * bx;
    C[c + wB * ty + tx] = Csub;
}

// __attribute__((global)) int bsize;

void matrixMul(float *C, float *A, float *B, int wA, int wB, int bsize)
{
    declare_logic_param("int m, hA");
    declare_precondition(
        "blockDim.x == bsize",
        "blockDim.y == bsize",
        "0 <= m",
        "wA == bsize * m",
        "wB == gridDim.x * bsize",
        "hA == gridDim.y * bsize");
    declare_postcondition(
        /* "forall i. forall j. */
        /*         0 <= i && i < hA && 0 <= j && j < wB -> */
        /*         C[wB * i + j] == sum(k, A[wA * i + k] * B[wB * k + j], 0, wA-1)" */
        /* easier to verify: */
        "forall i1. forall i2. forall j1. forall j2.
                0 <= i1 && i1 < gridDim.y && 0 <= i2 && i2 < bsize &&
                0 <= j1 && j1 < gridDim.x && 0 <= j2 && j2 < bsize ->
                C[wB * (i1 * bsize + i2) + (j1 * bsize + j2)] ==
                  sum(k, A[wA * (i1 * bsize + i2) + k] * B[wB * k + j1 * bsize + j2], 0, wA-1)");
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
    for (int a = aBegin, b = bBegin;
         a <= aEnd;
         a += aStep, b += bStep)
    {
        declare_invariant(
            "loop_count <= m",
            "a == aBegin + aStep * loop_count",
            "b == bBegin + bStep * loop_count",
            "Csub ==
                sum(k, A[wA * (bsize * by + ty) + k] * B[wB * k + bsize * bx + tx],
                    0, bsize * loop_count - 1)");
        __attribute__((shared)) float As[][], Bs[][];
        As[ty][tx] = A[a + wA * ty + tx];
        Bs[ty][tx] = B[b + wB * ty + tx];
        __syncthreads();
        for (int k = 0; k < bsize; ++k)
        {
            declare_invariant(
                "k == loop_count",
                "loop_count <= bsize",
                "Csub ==
                  sum(k, A[wA * (bsize * by + ty) + k] * B[wB * k + bsize * bx + tx],
                      0, bsize * loop_count_2 + loop_count - 1)");
            Csub += As[ty][k] * Bs[k][tx];
        }
        __syncthreads();
    }
    int c = wB * bsize * by + bsize * bx;
    C[c + wB * ty + tx] = Csub;
}

__attribute__((global)) int bsize_x;
__attribute__((global)) int bsize_y;

void matrixMul2(float *C, float *A, float *B, int wA, int wB)
{
    declare_logic_param(
        "int m",
        "int hA"
        );
    declare_precondition(
        "0 < bsize_x",
        // "bsize_y == 8",
        "bsize_x == 2 * bsize_y",
        "blockDim.x == bsize_x",
        "blockDim.y == bsize_y",
        "0 <= m",
        "wA == bsize_x * m",
        "wB == gridDim.x * bsize_x",
        "hA == gridDim.y * bsize_x"
        );
    declare_postcondition(
        /* "forall i. forall j. */
        /*         0 <= i && i < hA && 0 <= j && j < wB -> */
        /*         C[wB * i + j] == sum(k, A[wA * i + k] * B[wB * k + j], 0, wA-1)" */
        "forall i1. forall i2. forall j1. forall j2.
                0 <= i1 && i1 < gridDim.y && 0 <= i2 && i2 < 2 * bsize_y &&
                0 <= j1 && j1 < gridDim.x && 0 <= j2 && j2 < 2 * bsize_y ->
                C[wB * (i1 * 2 * bsize_y + i2) + j1 * 2 * bsize_y + j2] ==
                  sum(k, A[wA * (i1 * 2 * bsize_y + i2) + k] *
                                B[wB * k + j1 * 2 * bsize_y + j2],
                      0, wA-1)"
        );
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

    for (int a = aBegin, b = bBegin;
         a <= aEnd;
         a += aStep, b += bStep)
    {
        declare_invariant(
            "loop_count <= m",
            "a == aBegin + aStep * loop_count",
            "b == bBegin + bStep * loop_count",
            "Csub[0] ==
                sum(k, A[wA * (bsize_x * by + ty) + k] * B[wB * k + bsize_x * bx + tx],
                    0, bsize_x * loop_count - 1)",
            "Csub[1] ==
                sum(k, A[wA * (bsize_x * by + (ty + bsize_y)) + k] *
                        B[wB * k + bsize_x * bx + tx],
                    0, bsize_x * loop_count - 1)"
            /* "forall i. 0 <= i && i < 2 -> */
            /*     Csub[i] == */
            /*     sum(k, A[wA * (bsize_x * by + ty + bsize_y * i) + k] * */
            /*            B[wB * k + bsize_x * bx + tx], */
            /*         0, bsize_x * loop_count - 1)" */);
        __attribute__((shared)) float As[][];
        __attribute__((shared)) float Bs[][];

        As[ty][tx] = A[a + wA * ty + tx];
        Bs[ty][tx] = B[b + wB * ty + tx];
        As[ty + bsize_y][tx] = A[a + wA * (ty + bsize_y) + tx];
        Bs[ty + bsize_y][tx] = B[b + wB * (ty + bsize_y) + tx];
        __syncthreads();

        for (int k = 0; k < bsize_x; ++k)
        {
            declare_invariant(
                // "(exists t : thread. active(t)) -> forall t : thread. active(t)",
                "k == loop_count",
                "loop_count <= bsize_x",
                "Csub[0] ==
                  sum(k, A[wA * (bsize_x * by + ty) + k] * B[wB * k + bsize_x * bx + tx],
                      0, bsize_x * loop_count_2 + loop_count - 1)",
                "Csub[1] ==
                  sum(k, A[wA * (bsize_x * by + ty + bsize_y) + k] *
                           B[wB * k + bsize_x * bx + tx],
                      0, bsize_x * loop_count_2 + loop_count - 1)"
                /* "forall i. 0 <= i && i < 2 -> */
                /*         Csub[i] == */
                /*           sum(k, A[wA * (bsize_x * by + ty + bsize_y * i) + k] * */
                /*               B[wB * k + bsize_x * bx + tx], */
                /*               0, bsize_x * loop_count_2 + loop_count - 1)" */);
            Csub[0] += As[ty][k] * Bs[k][tx];
            Csub[1] += As[ty + bsize_y][k] * Bs[k][tx];
            /* for (int i = 0; i < 2; i++) { */
            /*     declare_invariant( */
            /*         // "(exists t : thread. active(t)) -> forall t : thread. active(t)", */
            /*         "i == loop_count", */
            /*         "loop_count <= 2", */
            /*         "forall j. 0 <= j && j < loop_count -> */
            /*             Csub[j] == */
            /*               sum(k, A[wA * (bsize_x * by + ty + bsize_y * j) + k] * */
            /*                   B[wB * k + bsize_x * bx + tx], */
            /*                   0, bsize_x * loop_count_3 + loop_count_2)", */
            /*         "forall j. loop_count <= j && j < 2 -> */
            /*             Csub[j] == */
            /*               sum(k, A[wA * (bsize_x * by + ty + bsize_y * j) + k] * */
            /*                   B[wB * k + bsize_x * bx + tx], */
            /*                   0, bsize_x * loop_count_3 + loop_count_2 - 1)"); */
            /*     Csub[i] += As[ty + bsize_y * i][k] * Bs[k][tx]; */
            /* } */
        }

        __syncthreads();
    }

    int c = wB * bsize_x * by + bsize_x * bx;
    C[c + wB * ty + tx] = Csub[0];
    C[c + wB * (ty + bsize_y) + tx] = Csub[1];
    // 変数名を j にすると証明できるけど i だとできないバグ -> Cil が rename している
    /* for (int j = 0; j < 2; j++) { */
    /*     declare_invariant( */
    /*         "j == loop_count", */
    /*         "loop_count <= 2", */
    /*         "forall j. 0 <= j && j < loop_count -> */
    /*             C[c + wB * (ty + bsize_y * j) + tx] == Csub[j]"); */
    /*     C[c + wB * (ty + bsize_y * j) + tx] = Csub[j]; */
    /* } */
}

void matrixMul4(float *C, float *A, float *B, int wA, int wB)
{
    declare_logic_param(
        "int m",
        "int hA"
        /* "int i, j", */
        /* "real dummy" */
        );
    declare_precondition(
        "0 < bsize_x",
        "bsize_x == 4 * bsize_y",
        "blockDim.x == bsize_x",
        "blockDim.y == bsize_y",
        "0 <= m",
        "wA == bsize_x * m",
        "wB == gridDim.x * bsize_x",
        "hA == gridDim.y * bsize_x"
        );
    declare_postcondition(
        "forall i1. forall i2. forall j1. forall j2.
                0 <= i1 && i1 < gridDim.y && 0 <= i2 && i2 < 4 * bsize_y &&
                0 <= j1 && j1 < gridDim.x && 0 <= j2 && j2 < 4 * bsize_y ->
                C[wB * (i1 * 4 * bsize_y + i2) + j1 * 4 * bsize_y + j2] ==
                  sum(k, A[wA * (i1 * 4 * bsize_y + i2) + k] * B[wB * k + j1 * 4 * bsize_y + j2], 0, wA-1)"
        );
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

    for (int a = aBegin, b = bBegin;
         a <= aEnd;
         a += aStep, b += bStep)
    {
        declare_invariant(
            "loop_count <= m",
            "a == aBegin + aStep * loop_count",
            "b == bBegin + bStep * loop_count",
            "Csub[0] ==
                sum(k, A[wA * (bsize_x * by + ty) + k] * B[wB * k + bsize_x * bx + tx],
                    0, bsize_x * loop_count - 1)",
            "Csub[1] ==
                sum(k, A[wA * (bsize_x * by + (ty + bsize_y)) + k] *
                        B[wB * k + bsize_x * bx + tx],
                    0, bsize_x * loop_count - 1)",
            "Csub[2] ==
                sum(k, A[wA * (bsize_x * by + (ty + 2 * bsize_y)) + k] *
                        B[wB * k + bsize_x * bx + tx],
                    0, bsize_x * loop_count - 1)",
            "Csub[3] ==
                sum(k, A[wA * (bsize_x * by + (ty + 3 * bsize_y)) + k] *
                        B[wB * k + bsize_x * bx + tx],
                    0, bsize_x * loop_count - 1)"
            /* "forall i. 0 <= i && i < 2 -> */
            /*     Csub[i] == */
            /*     sum(k, A[wA * (bsize_x * by + ty + bsize_y * i) + k] * */
            /*            B[wB * k + bsize_x * bx + tx], */
            /*         0, bsize_x * loop_count - 1)" */);
        __attribute__((shared)) float As[][];
        __attribute__((shared)) float Bs[][];

        As[ty][tx] = A[a + wA * ty + tx];
        Bs[ty][tx] = B[b + wB * ty + tx];
        As[ty + bsize_y][tx] = A[a + wA * (ty + bsize_y) + tx];
        Bs[ty + bsize_y][tx] = B[b + wB * (ty + bsize_y) + tx];
        As[ty + 2 * bsize_y][tx] = A[a + wA * (ty + 2 * bsize_y) + tx];
        Bs[ty + 2 * bsize_y][tx] = B[b + wB * (ty + 2 * bsize_y) + tx];
        As[ty + 3 * bsize_y][tx] = A[a + wA * (ty + 3 * bsize_y) + tx];
        Bs[ty + 3 * bsize_y][tx] = B[b + wB * (ty + 3 * bsize_y) + tx];
        __syncthreads();

        for (int k = 0; k < bsize_x; ++k)
        {
            declare_invariant(
                // "(exists t : thread. active(t)) -> forall t : thread. active(t)",
                "k == loop_count",
                "loop_count <= bsize_x",
                "Csub[0] ==
                  sum(k, A[wA * (bsize_x * by + ty) + k] * B[wB * k + bsize_x * bx + tx],
                      0, bsize_x * loop_count_2 + loop_count - 1)",
                "Csub[1] ==
                  sum(k, A[wA * (bsize_x * by + ty + bsize_y) + k] *
                           B[wB * k + bsize_x * bx + tx],
                      0, bsize_x * loop_count_2 + loop_count - 1)",
                "Csub[2] ==
                  sum(k, A[wA * (bsize_x * by + ty + 2 * bsize_y) + k] *
                           B[wB * k + bsize_x * bx + tx],
                      0, bsize_x * loop_count_2 + loop_count - 1)",
                "Csub[3] ==
                  sum(k, A[wA * (bsize_x * by + ty + 3 * bsize_y) + k] *
                           B[wB * k + bsize_x * bx + tx],
                      0, bsize_x * loop_count_2 + loop_count - 1)"
                /* "forall i. 0 <= i && i < 2 -> */
                /*         Csub[i] == */
                /*           sum(k, A[wA * (bsize_x * by + ty + bsize_y * i) + k] * */
                /*               B[wB * k + bsize_x * bx + tx], */
                /*               0, bsize_x * loop_count_2 + loop_count - 1)" */);
            Csub[0] += As[ty][k] * Bs[k][tx];
            Csub[1] += As[ty + bsize_y][k] * Bs[k][tx];
            Csub[2] += As[ty + 2 * bsize_y][k] * Bs[k][tx];
            Csub[3] += As[ty + 3 * bsize_y][k] * Bs[k][tx];
            /* for (int i = 0; i < 2; i++) { */
            /*     declare_invariant( */
            /*         // "(exists t : thread. active(t)) -> forall t : thread. active(t)", */
            /*         "i == loop_count", */
            /*         "loop_count <= 2", */
            /*         "forall j. 0 <= j && j < loop_count -> */
            /*             Csub[j] == */
            /*               sum(k, A[wA * (bsize_x * by + ty + bsize_y * j) + k] * */
            /*                   B[wB * k + bsize_x * bx + tx], */
            /*                   0, bsize_x * loop_count_3 + loop_count_2)", */
            /*         "forall j. loop_count <= j && j < 2 -> */
            /*             Csub[j] == */
            /*               sum(k, A[wA * (bsize_x * by + ty + bsize_y * j) + k] * */
            /*                   B[wB * k + bsize_x * bx + tx], */
            /*                   0, bsize_x * loop_count_3 + loop_count_2 - 1)"); */
            /*     Csub[i] += As[ty + bsize_y * i][k] * Bs[k][tx]; */
            /* } */
        }

        __syncthreads();
    }

    int c = wB * bsize_x * by + bsize_x * bx;
    C[c + wB * ty + tx] = Csub[0];
    C[c + wB * (ty + bsize_y) + tx] = Csub[1];
    C[c + wB * (ty + 2 * bsize_y) + tx] = Csub[2];
    C[c + wB * (ty + 3 * bsize_y) + tx] = Csub[3];
}

void matrixMulk(float *C, float *A, float *B, int wA, int wB, int k)
{
    declare_logic_param(
        "int m",
        "int hA",
        "int i0, j0",
        "real dummy");
    declare_precondition(
        "0 < bsize_y",
        "0 < k",
        "bsize_x == k * bsize_y",
        "blockDim.x == bsize_x",
        "blockDim.y == bsize_y",
        "0 <= m",
        "wA == bsize_x * m",
        "wB == gridDim.x * bsize_x",
        "hA == gridDim.y * bsize_x",
        "C[wB * i0 + j0] == dummy");
    declare_postcondition(
        /* "C[wB * i0 + j0] == sum(k, A[wA * i0 + k] * B[wB * k + j0], 0, wA-1) */
        /*  || C[wB * i0 + j0] == dummy" */
        "C[wB * i0 + j0] == sum(k, A[wA * i0 + k] * B[wB * k + j0], 0, wA-1)"
        );
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

    for (int i1 = 0; i1 < k; i1++) {
        declare_invariant(
            "i1 == loop_count", "loop_count <= k",
            "forall i. 0 <= i && i < i1 -> Csub[i] == 0");
        Csub[i1] = 0;
    }

    for (int a = aBegin, b = bBegin;
         a <= aEnd;
         a += aStep, b += bStep)
    {
        declare_invariant(
            "loop_count <= m",
            "a == aBegin + aStep * loop_count",
            "b == bBegin + bStep * loop_count",
            "forall i. 0 <= i && i < k ->
                Csub[i] ==
                sum(k, A[wA * (bsize_x * by + ty + bsize_y * i) + k] *
                       B[wB * k + bsize_x * bx + tx],
                    0, bsize_x * loop_count - 1)");
        __attribute__((shared)) float As[][];
        __attribute__((shared)) float Bs[][];

        for (int i0 = 0; i0 < k; i0++) {
            declare_invariant(
                "i0 == loop_count",
                "loop_count <= k",
                "forall i. 0 <= i && i < loop_count ->
                   As[ty + bsize_y * i][tx] == A[a + wA * (ty + bsize_y * i) + tx]",
                "forall i. 0 <= i && i < loop_count ->
                   Bs[ty + bsize_y * i][tx] == B[b + wB * (ty + bsize_y * i) + tx]");
            As[ty + bsize_y * i0][tx] = A[a + wA * (ty + bsize_y * i0) + tx];
            Bs[ty + bsize_y * i0][tx] = B[b + wB * (ty + bsize_y * i0) + tx];
        }
        __syncthreads();

        for (int l = 0; l < bsize_x; ++l)
        {
            declare_invariant(
                // "(exists t : thread. active(t)) -> forall t : thread. active(t)",
                "l == loop_count",
                "loop_count <= bsize_x",
                "forall i. 0 <= i && i < k ->
                        Csub[i] ==
                          sum(k, A[wA * (bsize_x * by + ty + bsize_y * i) + k] *
                              B[wB * k + bsize_x * bx + tx],
                              0, bsize_x * loop_count_2 + loop_count - 1)");
            for (int i = 0; i < k; i++) {
                declare_invariant(
                    // "(exists t : thread. active(t)) -> forall t : thread. active(t)",
                    "i == loop_count",
                    "loop_count <= k",
                    "forall j. 0 <= j && j < loop_count ->
                        Csub[j] ==
                          sum(k, A[wA * (bsize_x * by + ty + bsize_y * j) + k] *
                              B[wB * k + bsize_x * bx + tx],
                              0, bsize_x * loop_count_3 + loop_count_2)",
                    "forall j. loop_count <= j && j < k ->
                        Csub[j] ==
                          sum(k, A[wA * (bsize_x * by + ty + bsize_y * j) + k] *
                              B[wB * k + bsize_x * bx + tx],
                              0, bsize_x * loop_count_3 + loop_count_2 - 1)");
                Csub[i] += As[ty + bsize_y * i][l] * Bs[l][tx];
            }
        }

        __syncthreads();
    }

    int c = wB * bsize_x * by + bsize_x * bx;
    for (int j = 0; j < k; j++) {
        declare_invariant(
            "j == loop_count",
            "loop_count <= k",
            "forall j. 0 <= j && j < loop_count ->
                C[c + wB * (ty + bsize_y * j) + tx] == Csub[j]");
        C[c + wB * (ty + bsize_y * j) + tx] = Csub[j];
    }
}
