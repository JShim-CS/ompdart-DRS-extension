#define N 100
#include<stdio.h>
int main(int argc,char *argv[]){
  int i;
  int len = 100;
  int a[100];
  int b[100];
  int _ret_val_0;
  

  
 
  #pragma drd
  for (i = 0; i <= N - 1 - 1; i+=1) {
    if(i%2 == 0){
      a[i + 1] = a[i] + b[i];
    }else{
      a[i] = b[i];
    }
    
  }
 
  for (i = 0; i <= len - 1; i += 1) {
    printf("i=%d a[%d]=%d\n",i,i,a[i]);
  }
 
  _ret_val_0 = 0;
  return _ret_val_0;
}

