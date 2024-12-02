// #define N 100
// #include<stdio.h>
#include<omp.h>
#define N 100

/*
Ran test on each function, commenting out other functions that we are not testing.
For example, I commented out fp2,fp3,fp4,fp5,fp6 when testing fp1.
*/




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
    //fp1();    //fp  
    //fp2();    //fp
    //fp3();    //fp
    //fp4();    //fp
    //fp5();      //nfp
    //fp6();
    fp7();
    return 0;

}



