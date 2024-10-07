int main(int argc,char *argv[]){
  int i;
  int len = 100;
  int a[100];
  int b[100];
  int _ret_val_0;
  

  for (i = 0; i <= len - 1; i += 1) {
    a[i] = i;
    b[i] = i + 1;
  }
  
  #pragma drd
  for (i = 0; i <= len - 1 - 1; i++) {
    a[i + 1] = a[i] + b[i];
  }
 
  for (i = 0; i <= len - 1; i += 1) {
    printf("i=%d a[%d]=%d\n",i,i,a[i]);
  }
 
  _ret_val_0 = 0;
  return _ret_val_0;
}

