#include<omp.h>
#define N 100


void fp7(){
    int arr[1000];
    #pragma omp parallel for
    for(int i = 0; i < 10; i++){
        if(i*i*i >= 1000){
            arr[i%6 + 6*i] = arr[2*i];
        }
    }
}

int main(int argc, char* argv[]){
    fp7();
    return 0;

}



