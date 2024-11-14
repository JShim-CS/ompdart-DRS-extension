// #define N 100
// #include<stdio.h>
#include<omp.h>
#define N 100

void fp1(){
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

void fp2(){
    int size = 100;
    int a = N;
    int b = N*N;
    int arr[size];

    #pragma omp parallel for
    for(int i = 0; i < 99; i++){
        if(i == 100){
            arr[i] = arr[i+1] + i;
        }
    }

}

void fp3(){
    int size = 100;
    int a = N;
    int b = N*N;
    int arr[size];

    #pragma omp parallel for
    for(int i = 0; i < 10; i++){
        arr[i] = arr[i%10] + i;
    }

}

void fp4(){
    int size = 100;
    int a = N;
    int b = 0;
    int arr[size];

    #pragma omp parallel for
    for(int i = 0; i < 10; i++){
        if(a){
            arr[i] = arr[i] + 1;
        }
        
        if(b){
            arr[i+1] = arr[i+1] + 1;
        }
    }

}

void fp5(){
    int size = 100;
    int a = N;
    int b = 0;
    int arr[size];

    #pragma omp parallel for
    for(int i = 0; i < N; i++){
        if(a){
            arr[i] = arr[i] + 1;
        }
        
        for(int j = 0; j < 0; j++){
            arr[j+1] = arr[j+1] + 1;
        }
        
    }
}


void GPT4_FP() {
    int array[100]; // A simple integer array with 100 elements

    // Initialize the array with initial values
    for (int i = 0; i < 100; i++) {
        array[i] = i;
    }

    #pragma omp parallel for
    for (int i = 0; i < 10; i++) {
        int index = (i * 3) % 100;
        if (i == 11) { // This condition will never be true
            int temp = array[index]; // Read
            array[index] = temp * 2 - 1; // Write
        }
    }

    #pragma omp parallel for
    for (int i = 9; i >= 0; i--) {
        int index = (i * 7 + 1) % 100;
        if (i == 10) { // This condition will never be true
            int temp = array[index];
            array[index] = temp / 2 + 1;
        }
    }

    for (int i = 0; i < 10; i++) {
        int index = (i * 5 + 2) % 100;
        if (i == -1) { // This condition will never be true
            int temp = array[index];
            array[index] = temp * 3 - 2;
        }
    }

    for (int i = 10; i > 0; i--) {
        int index = (i * 2 + 3) % 100;
        if (i == 11) { // This condition will never be true
            int temp = array[index];
            array[index] = temp / 2 + 3;
        }
    }

    for (int i = 0; i < 10; i++) {
        int index = (i * 11 + 4) % 100;
        if (i == 15) { // This condition will never be true
            int temp = array[index];
            array[index] = temp * 4 - 4;
        }
    }

    for (int i = 9; i >= 0; i--) {
        int index = (i * 6 + 5) % 100;
        if (i == 11) { // This condition will never be true
            int temp = array[index];
            array[index] = temp / 3 + 5;
        }
    }

    for (int i = 0; i < 10; i++) {
        int index = (i * 8 + 6) % 100;
        if (i == 20) { // This condition will never be true
            int temp = array[index];
            array[index] = temp * 5 - 6;
        }
    }

    for (int i = 10; i > 0; i--) {
        int index = (i * 4 + 7) % 100;
        if (i == 12) { // This condition will never be true
            int temp = array[index];
            array[index] = temp / 4 + 7;
        }
    }

    for (int i = 0; i < 10; i++) {
        int index = (i * 9 + 8) % 100;
        if (i == -1) { // This condition will never be true
            int temp = array[index];
            array[index] = temp * 6 - 8;
        }
    }

    for (int i = 9; i >= 0; i--) {
        int index = (i * 10 + 9) % 100;
        if (i == 15) { // This condition will never be true
            int temp = array[index];
            array[index] = temp / 5 + 9;
        }
    }
}

static int arr[100];
int main(int argc, char* argv[]){
    int a  [100][200];
    #pragma drd
    for(int i = 0; i < 100;i++){
        for(int j = 0; j < 200;j++){
            for(int k = 0; k < 100; k++){
                if(i || j && k!=2){
                //arr[j+1] = NULL;
                //arr[k+1] = NULL;
                a  [i][j] = 0;
                argc = a[j][k] = argc;
                }
            }
        }

        //argv[i] = NULL;
        //argv[i+1] = NULL;
    }
    return 0;

}



