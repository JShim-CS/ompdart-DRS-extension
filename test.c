#include <omp.h>

int main(int argc, char *argv[]) {
    int histogramSize = 200000000;
    int histogram[histogramSize];

    for (int j = 0; j < histogramSize; j++) {
        histogram[j] = 0;
    }
   
    #pragma omp parallel for
    for (int i = 0; i < 100; i++) {
        if((i*i*i)%2 == 0){
            histogram[(i*i*i)] = i;
        }else if(i % 5 == 0){
            histogram[((i+1)*(i+1)*(i+1)*(i+1))] = 30*i;
        }
        else if(i % 13 == 0){
            histogram[((i-1)*(i-1)*(i-1)*(i-1))] = 40*i;
        }else if (i > 1){
            histogram[((i-1)*(i-1)*(i+2)*(i+3))] = 50*i; 
        }
    }
    return 0;
}
