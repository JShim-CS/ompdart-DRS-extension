// #define N 100
// #include<stdio.h>
#include<omp.h>
#define N 100

void fp1(){
    int size = 100;
    int a = N;
    int b = N*N;
    int arr[size];

    #pragma omp parallel for
    for(int i = 0; i < 99; i++){
        if(a == b){
            arr[i] = arr[i+1] + i;
        }
    }

}

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

void fp4(){
    int size = 100;
    int a = N;
    int b = 0;
    int arr[size];

    #pragma omp parallel for
    for(int i = 0; i < 10; i++){
        if(a){
            arr[i] = arr[i] + 1;
        }
        
        if(b){
            arr[i+1] = arr[i+1] + 1;
        }
    }

}

void fp5(){
    int size = 100;
    int a = N;
    int b = 0;
    int arr[size];

    #pragma omp parallel for
    #pragma drd
    for(int i = 0; i < N; i++){
        if(a){
            arr[i] = arr[i] + 1;
        }
        
        for(int j = 0; j < 0; j++){
            arr[j+1] = arr[j+1] + 1;
        }
        
    }
}

int main(int argc, char* argv[]){
    //fp1();    //fp  
    //fp2();    //fp
    //fp3();    //fp
    //fp4();    //fp
    fp5();      //nfp
    return 0;

}



