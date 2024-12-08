#include<omp.h>
#define N 100

void fp2(){ 
    int size = 100;
    int a = N;
    int b = N*N;
    int arr[size];

    #pragma omp parallel for
    for(int i = 0; i < 99; i++){
        if(i == 100){
            arr[i] = arr[i+1] + i;
        }
    }

}



int main(int argc, char* argv[]){
    fp2();    
    return 0;

}



