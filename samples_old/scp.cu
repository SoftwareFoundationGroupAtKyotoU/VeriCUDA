// taken from:
// https://fmt.ewi.utwente.nl/redmine/projects/vercors-verifier/wiki/Scp-examplepvl

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

void scp(int *a, int *b, int gsize) {
    // gsize == size of arrays
    declare_precondition("gsize == blockDim.x");
    declare_postcondition(
        "forall i. 0 <= i && i < gsize -> b[i] == (i+1) % gsize");
    int tid = threadIdx.x;
    a[tid] = tid;
    __syncthreads();
    b[tid] = a[(tid+1) % gsize];
}
