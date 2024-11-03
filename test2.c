// #define N 100
// #include<stdio.h>
int main(int argc,char *argv[]){
  //int i;
  int arr[10];
  #pragma drd
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

