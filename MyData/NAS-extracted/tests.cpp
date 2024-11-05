#include<omp.h>
#define N 100
// void NAS_cg(){
//     int rowstr[100];
//     int j;
//     int nrows = 100;
//     #pragma omp parallel for
//     //#pragma drd
//     for (j = nrows; j >= 1; j--) {
// 	    rowstr[j+1] = rowstr[j];
//     }
// }

// //false negative on WAW
// void GPTO1_WAW1() {
//     int size = 100;
//     int array[size];
//     #pragma omp parallel for
//     //#pragma drd
//     for (int i = 0; i < size; i++) {
//         array[0] = i;
//     }
// }

// void GPTO1_WAR1(){
//     int size = 100;
//     int array[size];
//     array[0] = 0;
//     #pragma omp parallel for
//     //#pragma drd
//     for (int i = 0; i < size; i++) {
//         //array[0] += array[i]; //doesn't work for drd 
//         array[0] = array[0] + array[i];
//     }
// }

// void GPTO1_WAR2(){
//      int size = 100;
//     int array[size];

//     #pragma omp parallel for
//     //#pragma drd
//     for (int i = 0; i < size - 1; i++) {
//         array[i + 1] = array[i] + 1;
//     }
// }

// void GPTO1_WARCNTRL1(int threshold){
//     int size = 100;
//     int array[size];
//     array[0] = 0;

//     //preprocessing for Tsan, this part was not written by GPT
//     for(int i = 0; i < size; i++){
//         array[i] = 30;
//     }
    
//     #pragma omp parallel for
//     //#pragma drd
//     for (int i = 0; i < size; i++) {
//         if (array[i] > threshold) {
//             array[0] = array[i];
//         }
//     }

// }

// void GPTO1_WARCNTRL2(int flag){
//     int size = 100;
//     int array[size];
//     array[0] = 0;

//     //preprocessing for Tsan, this part was not written by GPT
//     for(int i = 0; i < size; i++){
//         array[i] = 30;
//     }

//     #pragma omp parallel for
//     //#pragma drd
//     for (int i = 0; i < size; i++) {
//         if (flag) {
//             array[i] = array[0];
//         } else {
//             array[0] = array[i];
//         }
//     }
// }

// void GPTO1_WAR3(){
//     int size = 100;
//     int array[size];
//     array[0] = 0;
//     //j's range is not specified in the algo. update it
//     #pragma omp parallel for
//     //#pragma drd
//     for (int i = 0; i < size; i++) {
//         for (int j = 0; j < size; j++) {
//             array[j] = array[i] + j;
//         }
//     }
// }

// void GPTO1_WAR4(){
//     int size = 100;
//     int array[size];
//     array[0] = 0;
//     int threshold = 10;
//     #pragma omp parallel for
//     //#pragma drd
//     for (int i = 0; i < size; i++) {
//         if (array[i] > threshold) {
//             //-= causes bug
//             array[i % 2] = array[i%2] - array[i];
//         }
//     }
// }

void GPT4_DATA_RACE(){
    int size = 100;
    int array[size];

    // // Loop 1
    // #pragma omp parallel for
    // //#pragma drd
    // for (int i = 0; i < 100; i++) {
    //     if (i % 10 == 0 && i % 20 != 0)
    //         array[i % 10] = array[i];
    // }

    // // Loop 2
    // #pragma omp parallel for
    // //#pragma drd
    // for (int i = 0; i < 100; i++) {
    //     if (i < 50 || i > 70)
    //         array[(i + 30) % 50] = array[i];
    // }

    // // Loop 3
    // #pragma omp parallel for
    // //#pragma drd
    // for (int i = 0; i < 90; i += 3) {
    //     if (i % 15 == 0 && i % 30 != 0)
    //         array[i % 20] = array[i];
    // }

    // // Loop 4
    // #pragma omp parallel for
    // //#pragma drd
    // for (int i = 1; i < 100; i++) {
    //     if ((i < 40 && i > 20) || (i < 80 && i > 60))
    //         array[(i * 2) % 25] = array[i];
    // }

    // // Loop 5
    // #pragma omp parallel for
    // //#pragma drd
    // for (int i = 0; i < 100; i += 2) {
    //     if (i % 6 == 0 || i % 18 == 0)
    //         array[i % 15] = array[i];
    // }

    // // Loop 6
    // #pragma omp parallel for
    // //#pragma drd
    // for (int j = 0; j < 100; j++) {
    //     for (int k = 0; k < 10; k++) {
    //         if (j % 10 == k && k < 5)
    //             array[j % 20] = array[j] + j + k;
    //     }
    // }

    // // Loop 7
    // #pragma omp parallel for
    // //#pragma drd
    // for (int i = 0; i < 60; i++) {
    //     if ((i < 30 || i > 45) && i % 5 == 0)
    //         array[(i * 3) % 40] = array[i];
    // }

    // // Loop 8
    // #pragma omp parallel for
    // //#pragma drd
    // for (int i = 0; i < 100; i++) {
    //     if (i % 4 == 0 || i % 6 == 0)
    //         array[(i + 10) % 30] = array[i];
    // }

    // Loop 9
    // #pragma omp parallel for
    // //#pragma drd
    // for (int i = 0; i < 120; i += 4) {
    //     if (i % 24 == 0 && i < 100)
    //         array[(i / 4) % 25] = i + array[i];
    // }

    // // Loop 10
    // #pragma omp parallel for
    // //#pragma drd
    // for (int i = 0; i < 100; i++) {
    //     if ((i < 25 || i > 75) && i % 7 == 0)
    //         array[(i * 2) % 40] = i - array[i];
    // }
} 


void hand_written(){
    int size = 100;
    int arr[size];
   
    // //loop 1
    // #pragma omp parallel for
    // #pragma drd
    // for(int i = 0; i < size-1; i++){
    //     for(int j = 0; j < size; j++){
    //         if(j != i && i <= 10){
    //             arr[i] = arr[i+1] * (i+j);
    //         }
    //     }
    // }

    //loop 2
    // #pragma omp parallel for
    // #pragma drd
    // for(int i = 0; i < size; i++){
    //     if(i != 0 ){
    //         arr[i] = arr[i+1];
    //     }
    // }

    //loop 3
    // #pragma omp parallel for
    // #pragma drd
    // for(int i = 0; i < size-1; i++){
    //     for(int k = 0; k < size; k++){
    //         for(int j = 0; j < size; j++){
    //             if(i != 0 || j != 0){
    //                 arr[i] = arr[i+1] + j + k - i;
    //             }
    //         }
    //     }
    // }

    //loop4
    // #pragma omp parallel for
    // #pragma drd
    // for(int i = 0; i < size-1; i++){
    //     arr[8] = arr[7];
    //     arr[7] = arr[8];
    // }

    // //loop5
    // #pragma omp parallel for
    // #pragma drd
    // for(int i = 0; i < size-1; i++){
    //     if(!(i == 0 || i == 1 || i == 2 || i == 3)){
    //         arr[i] = arr[i+1] + i;
    //     }
          
    // }

    // //loop6
    // #pragma omp parallel for
    // #pragma drd
    // for(int i = 0; i < size-1; i++){
    //     if(!(i <= 20 && i >= 5)){
    //         arr[i] = arr[i+1] + i;
    //     }
          
    // }

    //loop7
    // #pragma omp parallel for
    // for(int i = 0; i < size-1; i++){
    //     if(i+8+i*i - i + i/2 + i + 2 == 10 || 8*i +2*i == 10 || 3*i + 2*i == 10 ){
    //         arr[i] = arr[i+1] + i;
    //     }
    // }

    // //loop8
    // #pragma omp parallel for
    // #pragma drd
    // for(int i = 0; i < size-1; i++){
    //     if(N == 200 && i != 0){
    //         arr[i] = arr[i+1] + i;
    //     }
        
    // }

    //loop9
    // #pragma omp parallel for
    // #pragma drd
    // for(int i = 0; i < size-1; i++){
    //     if(i != 0 && i != 1 && i != 2 && i != 3 && i <= 20){
    //         arr[i] = arr[i+1] + i;
    //     }
        
    // }

    // //loop10
    // #pragma omp parallel for
    // #pragma drd
    // for(int i = 0; i < size-1; i++){
    //     if(i != 0){
    //         arr[i] = i;
    //     }else{
    //         arr[i+1] = 3;
    //     }
        
    // }



    
    

    
}




int main(int argc, char *argv[]){
    //NAS_cg();
    //GPTO1_WAW1();
    //GPTO1_WAR1();
    //GPTO1_WARCNTRL1(10);
    //GPTO1_WARCNTRL2(1);
    //GPTO1_WAR2();
    //GPTO1_WAR3();
    //GPTO1_WAR4();
    // int arr[100];
    // #pragma omp parallel for
    // //
    // for(int i = 0; i < 100; i++){
    //     for(int k = 0; k <= i; k++){
    //         if(k%2 == 0 && i + 1 == 4){
    //             arr[i] += i*k;
    //         }
    //     }
    //     arr[i+1] = arr[i] + 1;
    // }

    //hand_written();
    GPT4_DATA_RACE();
    return 0;
}