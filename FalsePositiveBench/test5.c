#include<omp.h>
#define N 100



void fp5(){
    int size = 100;
    int a = N;
    int b = 0;
    int arr[size];

    #pragma omp parallel for
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
    fp5();      
    return 0;

}



