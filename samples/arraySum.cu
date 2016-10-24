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
arraySum_0(const int *A, const int *S, unsigned int n)
{
    declare_logic_param("int m");
    declare_precondition(
        "0 < m",
        // "forall t1 : thread. forall t2 : thread. numElements@t1 == numElements@t2",
        "blockDim.x == 2 ^ m",
        "forall i. A[i] == 1");
    declare_postcondition("S[blockIdx.x] == blockDim.x");
    // declare_postcondition("S[blockIdx.x] == sum(i, A[i + blockDim.x * blockIdx.x], 0, blockDim.x - 1");

    __attribute__((shared)) int sdata[];
    unsigned int i = blockDim.x * blockIdx.x + threadIdx.x;

    sdata[threadIdx.x] = A[i]; //(i < n) ? A[i] : 0;

    __syncthreads();

    for (unsigned int s = blockDim.x/2; s > 0; s /= 2)
    {
        declare_invariant(
            "s >= 0",
            "s > 0 -> s == 2 ^ (m - loop_count - 1)",
            "0 <= loop_count && loop_count <= m",
            "forall i.
                0 <= i && i < 2 * s ->
                sdata[i] == 2^loop_count");
        if (threadIdx.x < s) sdata[threadIdx.x] += sdata[threadIdx.x + s];
        __syncthreads();
    }

    assert("sdata[0] == blockDim.x");
    if (threadIdx.x == 0) S[blockIdx.x] = sdata[0];
}
