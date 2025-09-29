#include <omp.h>

int main(int argc, char *argv[]) {
    int arr[2000];
    #pragma drs
    for(int i = 0; i < 200; i++){
        arr[i%20] = 1;
    }
    
    return 0;
}
