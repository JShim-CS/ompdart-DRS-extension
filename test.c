#include<omp.h>

void func(){
    int a[1000];
    #pragma omp target
    for(int i = 0; i < 1000; i++){
        a[i] = i;
    }
    
    #pragma omp target
    for(int i = 0; i < 1000; i++){
        a[i] *= i;
    }

}