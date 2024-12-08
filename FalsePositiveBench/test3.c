#include<omp.h>
#define N 100



void fp3(){
    int size = 100;
    int a = N;
    int b = N*N;
    int arr[size];

    #pragma omp parallel for
    for(int i = 0; i < 10; i++){
        arr[i] = arr[i%10] + i;
    }

}

int main(int argc, char* argv[]){
    fp3();    
    return 0;

}



