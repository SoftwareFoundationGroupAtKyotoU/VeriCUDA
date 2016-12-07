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

void rotate(int *a, int size) {
    declare_logic_param(
        "int a0[]"
        );
    declare_precondition(
        "size == blockDim.x",
        "forall i. a[i] == a0[i]"
        );
    declare_postcondition(
        "forall i. 0 < i && i < size - 1 -> a[i] == a0[i - 1]",
        "a[0] == a0[size - 1]"
        );
    int tmp = a[threadIdx.x];
    int t = threadIdx.x + 1;
    if (t == size) t = 0;
    __syncthreads();
    a[t] = tmp;
}
