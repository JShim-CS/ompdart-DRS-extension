#include<omp.h>

void func(){
    
    int a[1000];

    #pragma drd
    for(int i = 0; i < 1000; i++){
        a[i] = i;
    }
    
    #pragma omp target map(to:a)
    for(int j = 0; j < 1000; j++){
        a[j] *= j;
    }

}