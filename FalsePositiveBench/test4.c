#include<omp.h>
#define N 100



void fp4(){
    int size = N;
    const int a = N;
    const int b = 0;
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



int main(int argc, char* argv[]){
    fp4();    
    return 0;

}



