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

// __global__ 
void
vectorAdd1(const float *A, const float *B, float *C, int numElements)
{
    declare_precondition(
        "0 <= numElements",
        "numElements < gridDim.x * blockDim.x"
        );
    declare_postcondition(
        "forall i. 0 <= i -> i < numElements -> C[i] == A[i] + B[i]");

    int i = blockDim.x * blockIdx.x + threadIdx.x;

    if (i < numElements)
    {
        C[i] = A[i] + B[i];
    }
}

/* void */
/* vectorAdd_no_opt(const float *A, const float *B, float *C, int numElements, int w) */
/* { */
/*     declare_precondition( */
/*         "forall t1 : thread. forall t2 : thread. numElements@t1 == numElements@t2"); */
/*     declare_precondition( */
/*         "forall t : thread. (blockDim.x * gridDim.x) * w <= numElements@t"); */
/*     declare_postcondition( */
/*         "forall t : thread. */
/*                 forall i. 0 <= i -> i < numElements@t -> C[i] == A[i] + B[i]"); */

/*     int i = blockDim.x * blockIdx.x + threadIdx.x; */
/*     int w = 1 + (numElements - 1) / (blockDim.x * gridDim.x); */

/*     for (int j = 0; j < w; j++) */
/*     { */
/*         declare_invariant( */
/*             "forall t : thread. */
/*                 forall k. i@t * w@t <= k -> k < i@t * w@t + j@t -> */
/*                 C[k] == A[k] + B[k]"); */
/*         C[i * w + j] = A[i * w + j] + B[i * w + j]; */
/*     } */
/* } */


void
vectorAdd(const float *A, const float *B, float *C, int numElements)
{
    declare_logic_param("int m");
    declare_precondition(
        // "m >= 0",
        /* "blockDim.x == 2", */
        /* "gridDim.x == 16", */
        "numElements == m * blockDim.x * gridDim.x");
    declare_postcondition(
        "forall i [C[i]]. 0 <= i -> i < numElements -> C[i] == A[i] + B[i]");

    int i = blockDim.x * blockIdx.x + threadIdx.x;

    while (i < numElements)
    {
        declare_invariant(
            "(exists t : thread. active(t)) -> forall t : thread. active(t)",
            "i == loop_count * blockDim.x * gridDim.x +
                blockDim.x * blockIdx.x + threadIdx.x",
            /* "forall t : thread. */
            /*     forall k1. 0 <= k1 && k1 < loop_count -> */
            /*       C[(blockIdx.x * blockDim.x + threadIdx.x + */
            /*               (gridDim.x * blockDim.x) * k1)@t] == */
            /*       A[(blockIdx.x * blockDim.x + threadIdx.x + */
            /*               (gridDim.x * blockDim.x) * k1)@t] + */
            /*       B[(blockIdx.x * blockDim.x + threadIdx.x + */
            /*               (gridDim.x * blockDim.x) * k1)@t]" */
            /* "loop_count <= m", */
            "forall k [C[k]]. 0 <= k && k < blockDim.x * gridDim.x * loop_count ->
                        C[k] == A[k] + B[k]"
            /* "forall j. 0 <= j && j <= i - gridDim.x * blockDim.x -> */
            /*    C[j] == A[j] + B[j]" */
            );
        C[i] = A[i] + B[i];
        i += gridDim.x * blockDim.x;
    }
}

void
vectorAdd_non_unif(const float *A, const float *B, float *C, int numElements)
{
    declare_precondition("numElements > 0");
    declare_postcondition(
        "forall i. 0 <= i -> i < numElements -> C[i] == A[i] + B[i]");

    int i = blockDim.x * blockIdx.x + threadIdx.x;

    while (i < numElements)
    {
        declare_invariant(
            /* "forall t : thread. */
            /*     active(t) ->  */
            /*       i@t == loop_count * blockDim.x * gridDim.x + */
            /*               blockDim.x * blockIdx.x + threadIdx.x", */
            /* "forall t : thread. */
            /*     !active(t) -> */
            /*       i@t == (loop_count - 1) * blockDim.x * gridDim.x + */
            /*               blockDim.x * blockIdx.x + threadIdx.x", */
            "(loop_count - 1) * blockDim.x * gridDim.x +
                blockDim.x * blockIdx.x + threadIdx.x < numElements ->
                i == loop_count * blockDim.x * gridDim.x +
                    blockDim.x * blockIdx.x + threadIdx.x",
            "(loop_count - 1) * blockDim.x * gridDim.x +
                blockDim.x * blockIdx.x + threadIdx.x >= numElements ->
                i == (loop_count - 1) * blockDim.x * gridDim.x +
                    blockDim.x * blockIdx.x + threadIdx.x",
            "forall k. 0 <= k && k < blockDim.x * gridDim.x * loop_count
                        && k < numElements ->
                          C[k] == A[k] + B[k]"
            );
        C[i] = A[i] + B[i];
        i += gridDim.x * blockDim.x;
    }
}

void
vectorAddDownward(const float *A, const float *B, float *C, int numElements)
{
    declare_logic_param("int m");
    declare_precondition(
        "numElements == m * blockDim.x * gridDim.x");
    declare_postcondition(
        "forall i [C[i]]. 0 <= i -> i < numElements -> C[i] == A[i] + B[i]");

    int i = numElements - 1 - blockDim.x * blockIdx.x - threadIdx.x;

    while (0 <= i)
    {
        declare_invariant(
            "(exists t : thread. active(t)) -> forall t : thread. active(t)",
            "i == numElements - 1 - loop_count * blockDim.x * gridDim.x -
                blockDim.x * blockIdx.x - threadIdx.x",
            "forall k [C[k]]. numElements - blockDim.x * gridDim.x * loop_count <= k && k < numElements ->
                        C[k] == A[k] + B[k]"
            );
        C[i] = A[i] + B[i];
        i -= gridDim.x * blockDim.x;
    }
}

