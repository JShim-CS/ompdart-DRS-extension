// #define N 100
// #include<stdio.h>
#include<omp.h>
#define N 100
void a(){
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


int main(int argc,char *argv[]){
  //int i;
  int arr[10];
  //#pragma drd

  #pragma omp parallel for
  for(int i=0; i < 10; i++){
    for(int k = 0; k < 10; k++){
      if(i == 0){
        arr[i+k] = arr[k];
      }else{
        arr[i+k+2] = arr[k] + 2;
      }
    }
  }
}

