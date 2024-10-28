///////////////////////////////////////////////////////////////////////////////
// matmul.c
// Author: Dr. Richard A. Goodrum, Ph.D.
//
// Procedures:
//
// main	generates matrices and tests matmul
// matmul	basic, brute force matrix multiply
///////////////////////////////////////////////////////////////////////////////
#include <stdio.h>
#include <sys/time.h>
#include "omp.h"
#include <omp.h> 
//int dummyMethod1();
//int dummyMethod2();
//int dummyMethod3();
//int dummyMethod4();
///////////////////////////////////////////////////////////////////////////////
// int main(int argc, char *argv[])
// Author: Dr. Richard A. Goodrum, Ph.D.
// Date:  16September 2017
// Modified by: Naman Gangwani
// Date: 31January 2018
// Description: Multiplies two matrices 
//              and stores the results into a third matrix.
//
// Parameters:
//	l	I/P	int	The first dimension of A and C
//	m	I/P	int	The second dimension of A and  first of B
//	n	I/P	int	The second dimension of B and C
//	A	I/P	float *	The first input matrix
//	B	I/P	float *	The second input matrix
//	C	O/P	float *	The output matrix
//	matmul	O/P	int	Status code
///////////////////////////////////////////////////////////////////////////////

//int matmul(int l,int m,int n,float *A,float *B,float *C)
//{
//  int i;
//  int j;
//  int k;
//  int result;
  //dummyMethod1();
  //for (i = 0; i <= l - 1; i += 1) {
// For each row of A and C
  //  for (k = 0; k <= n - 1; k += 1) 
// For each column of B and C
//{
//      result = 0;
/* Take the dot product of the row of A with the column of B */
      
//#pragma omp parallel for private (j) reduction (+:result)
//#pragma rose_outline
     // for (j = 0; j <= m - 1; j += 1) 
// For each column of A
//{
// Add single component of dot product
//        result += A[i * m + j] * B[j * n + k];
//      }
//      C[i * n + k] = result;
// Save the dot product into C
//    }
//  }
 // dummyMethod2();
//}
///////////////////////////////////////////////////////////////////////////////
// int main(int argc, char *argv[])
// Author: Dr. Richard A. Goodrum, Ph.D.
// Date:  16September 2017
// Description: Generates two matrices and then calls matmul to multiply them.
// 	Finally, it verifies that the results are correct.
//
// Parameters:
//	argc	I/P	int	The number of arguments on the command line
//	argv	I/P	char *[]	The arguments on the command line
//	main	O/P	int	Status code
///////////////////////////////////////////////////////////////////////////////
#define L (250*1024/256)
#define M (250*1024/256)
#define N (250*1024/256)
//#define DEBUG 1
float A[1000000];
float B[1000000];
float C[1000000];

int main(int argc,char *argv[])
{
  int i;
  int j;
  int k;
/* Populates A array to an upper triangular matrix of various numbers*/
  //dummyMethod3();
  
  //for (i = 0; i <= 999; i += 1) {
// Loops through A's first dimension
    
//#pragma omp parallel for private (j)
//#pragma rose_outline
    #pragma drd
    for (j = 0; j <= 999; j += 1) {
// Loops through A's second dimension
      if (i <= j) 
// If it is in the upper triangle or diagonal
{
        A[i * (250 * 1024 / 256) + j] = ((float )(i * (250 * 1024 / 256) + j + 1));
// Compute a value for it
      }
       else {
        A[i * (250 * 1024 / 256) + j] = 0.0;
// Otherwise, it is 0 in lower triangle
//A[i*M+j] = (float) (i*M+j+1);
      }
    }
  //}
//   dummyMethod4();
// /* Populates B array iteratively */
//   dummyMethod3();
//   for (j = 0; j <= 999; j += 1) {
// // Loops through B's first dimension
//     for (k = 0; k <= 999; k += 1) {
// // Loops through B's second dimension
//       if (j <= k) 
// // If it's in the upper triangle or diagonal
// {
// // If it is a part of the square part of the matrix
//         if (k < 250 * 1024 / 256) 
//           B[j * (250 * 1024 / 256) + k] = 1.0;
//          else 
// // Set it to 1
// //Otherwise, set it to be one plus the previous value of its row
//           B[j * (250 * 1024 / 256) + k] = (B[j * (250 * 1024 / 256) + k - 1] + 1.0);
//       }
//        else {
//         B[j * (250 * 1024 / 256) + k] = 0.0;
// // Otherwise, it is 0 in lower triangle
//       }
//     }
//   }
//   dummyMethod4();
// /* Populates C array  with temporary numbers*/
//   dummyMethod3();
// // Loops through C's first dimension
  

//   for (i = 0; i <= 999; i += 1) {
// // Loops through C's second dimension
    
// #pragma omp parallel for private (k)
// //#pragma rose_outline
//     for (k = 0; k <= 999; k += 1) {
//       C[i * (250 * 1024 / 256) + k] = -((float )(250 * 1024 / 256)) * (250 * 1024 / 256) * (250 * 1024 / 256);
//     }
//   }
// // Assigns it to an arbritrary value
//   dummyMethod4();
//   struct timeval start;
//   struct timeval stop;
// // Struct to keep track of execution time
//   gettimeofday(&start,(void *)0);
// // Start time before matrix multiplication
//   matmul(250 * 1024 / 256,250 * 1024 / 256,250 * 1024 / 256,A,B,C);
//   gettimeofday(&stop,(void *)0);
// // End time after matrix multiplication
//   float elapsed = (stop . tv_sec - start . tv_sec) + (stop . tv_usec - start . tv_usec) / ((float )1000000);
// // Calculates the amount of time elapsed during matrix multiplication
// // Number of floating point operations per second that occurred during matrix multiplication
//   float flops = 2 * ((float )(250 * 1024 / 256)) * ((float )(250 * 1024 / 256)) * ((float )(250 * 1024 / 256)) / elapsed;
// // Outputs the information and statistics of the matrix multiplication algorithm
//   printf("L = %d, M = %d, N = %d, elapsed = %g, flops = %g\n",250 * 1024 / 256,250 * 1024 / 256,250 * 1024 / 256,elapsed,flops);
//   printf("\n");
// /* Prints matrices to check for correctness only if DEBUG mode is on */
// #ifdef DEBUG
// /* Print the A matrix */
// // For each row
// // For each column of each row
// // Print value at that position
// /* Print the B matrix */
// // For each row
// // For each column of each row
// // Print value at that position
// /* Print the C matrix */
// // For each row
// // For each column of each row
// #endif

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
