#include<omp.h>
#define N 100

void fp1(){ 
    int size = 100;
    int a = N;
    int b = N*N;
    int arr[size];

    #pragma drs
    for(int i = 0; i < 99; i++){
        if(a == b){
            arr[i] = arr[i+1] + i;
        }
    }

}



int main(int argc, char* argv[]){
    fp1();    
    return 0;

}



