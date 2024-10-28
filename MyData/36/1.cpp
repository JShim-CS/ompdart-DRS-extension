#include <stdio.h>
#include <omp.h>
int dummyMethod1();
int dummyMethod2();
int dummyMethod3();
int dummyMethod4();
int main()
{
  int i;
  int len = 1000;
  int a[1000];

//commented out for intel inspector
// #pragma omp parallel for private(i)
// //#pragma rose_outline
//   for (i=0; i<len; i++){
//     a[i]= i;
//   }

dummyMethod3();
  #pragma omp parallel for private(i) //manually added to check with thread_sanitizer
  for (i=0;i< len -1 ;i++){
    a[i]=a[i+1]+1;
  }

dummyMethod4();
  return 0;
dummyMethod2();
}
int dummyMethod1(){
    return 0;
}
int dummyMethod2(){
    return 0;
}
int dummyMethod3(){
    return 0;
}
int dummyMethod4(){
    return 0;
}