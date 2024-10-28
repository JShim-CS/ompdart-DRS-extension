#include <math.h>
#include "omp.h"
#include <stdlib.h>
#include <stdio.h>
#include <sys/time.h>
#include <omp.h> 
// int dummyMethod1();
// int dummyMethod2();
// int dummyMethod3();
// int dummyMethod4();
// /* Row-major order macro */
// #define RM(row,col) ((row) + ((2)*(col)))

// double gettime()
// {
//   struct timeval tv;
//   gettimeofday(&tv,(void *)0);
//   return tv . tv_sec + 1e-6 * tv . tv_usec;
// }

int main(int argc,char **argv)
{
  int i;
  int j;
  int dN;
  int tid;
  int Nthrds;
  int start;
  int end;
  int MaxNthrds;
  double dw;
  double fprt;
  double locsum;
  double dtime;
  double *A;
  double *blocksum;
  int N = 12123123;
  omp_lock_t *locks;
#ifdef _OPENMP
#else
  MaxNthrds = 1;
#endif
  A = (calloc((2 * N),sizeof(double )));
  blocksum = (calloc(MaxNthrds,sizeof(double )));
  dw = 3.14159265358979323846 / ((double )N);
//   dummyMethod3();
  
// #pragma omp parallel for private (i) firstprivate (dw)
// //#pragma rose_outline
//   for (i = 0; i <= N - 1; i += 1) {
//     A[0 + 2 * i] = i * dw;
//   }
//   dummyMethod4();
//   dummyMethod3();
  
  #pragma drd
  for (i = 0; i <= N - 1; i += 1) {
    A[1 + 2 * i] = A[0 + 2 * i];
  }
  // dummyMethod4();
  // double n = 0;
  // dtime = gettime();
  // dummyMethod1();
  
// #pragma omp parallel for private (i) reduction (+:n)
// //#pragma rose_outline
//   for (i = 0; i <= N - 1; i += 1) {
//     n += A[0 + 2 * i];
//   }
//   dummyMethod2();
//   printf("First summation loop took  %9.5f seconds\n",gettime() - dtime);
// /*--------------------------------------------------------------------------*/
//   dtime = gettime();
//   dummyMethod3();
//   for (i = 1; i <= N - 1; i += 1) {
//     A[1 + 2 * i] = A[1 + 2 * (i - 1)] + A[1 + 2 * i];
//   }
//   dummyMethod4();
//   printf("Second summation loop took %9.5f seconds\n",gettime() - dtime);
//   printf("%e %e\n",n,A[1 + 2 * (N - 1)]);
//   free(blocksum);
//   free(A);
  return 0;
}

// int dummyMethod1()
// {
//   return 0;
// }

// int dummyMethod2()
// {
//   return 0;
// }

// int dummyMethod3()
// {
//   return 0;
// }

// int dummyMethod4()
// {
//   return 0;
// }
