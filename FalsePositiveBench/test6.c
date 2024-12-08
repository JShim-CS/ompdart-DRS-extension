#include<omp.h>
#define N 100


void fp6(){
    int size = 100;
    int a = 0;
    int b = N;
    int arr[size];

    #pragma omp parallel for
    for(int i = 0; i < N; i++){
        if(a == 0 && b != N){
            arr[i] = arr[i] + 1;
            arr[i] = arr[i+1] + 1;
        }
    }
}




int main(int argc, char* argv[]){
    //fp1();    //fp  
    //fp2();    //fp
    //fp3();    //fp
    //fp4();    //fp
    //fp5();      //nfp
    fp6();
    //fp7();
    return 0;

}



