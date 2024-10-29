// RUN: clang %loadLLOV %s -o /dev/null 2>&1 | FileCheck %s
#include "omp.h"
#include <omp.h> 
int dummyMethod1();
int dummyMethod2();
int dummyMethod3();
int dummyMethod4();
#define N 20

int main()
{
  int A[20][20][20];
  dummyMethod1();
  
  for (int i = 1; i <= 19; i += 1) {
    for (int j = 1; j <= 19; j += 1) {
      
#pragma omp parallel for
//#pragma rose_outline
      for (int k = 1; k <= 19; k += 1) {
        A[i][j][k] = A[i][j - 1][k];
      }
    }
  }
}
int dummyMethod2();
// CHECK: Region is Data Race Free.
// END

int dummyMethod1()
{
  return 0;
}

int dummyMethod2()
{
  return 0;
}

int dummyMethod3()
{
  return 0;
}

int dummyMethod4()
{
  return 0;
}
