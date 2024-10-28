#include<omp.h>

void NAS_cg(){
    int rowstr[100];
    int j;
    int nrows = 100;
    #pragma omp parallel for
    //#pragma drd
    for (j = nrows; j >= 1; j--) {
	    rowstr[j+1] = rowstr[j];
    }
}

//false negative on WAW
void GPTO1_WAW1() {
    int size = 100;
    int array[size];
    #pragma omp parallel for
    //#pragma drd
    for (int i = 0; i < size; i++) {
        array[0] = i;
    }
}

void GPTO1_WAR1(){
    int size = 100;
    int array[size];
    array[0] = 0;
    #pragma omp parallel for
    //#pragma drd
    for (int i = 0; i < size; i++) {
        //array[0] += array[i]; //doesn't work for drd 
        array[0] = array[0] + array[i];
    }
}

void GPTO1_WAR2(){
     int size = 100;
    int array[size];

    #pragma omp parallel for
    //#pragma drd
    for (int i = 0; i < size - 1; i++) {
        array[i + 1] = array[i] + 1;
    }
}

void GPTO1_WARCNTRL1(int threshold){
    int size = 100;
    int array[size];
    array[0] = 0;

    //preprocessing for Tsan, this part was not written by GPT
    for(int i = 0; i < size; i++){
        array[i] = 30;
    }
    
    #pragma omp parallel for
    //#pragma drd
    for (int i = 0; i < size; i++) {
        if (array[i] > threshold) {
            array[0] = array[i];
        }
    }

}

void GPTO1_WARCNTRL2(int flag){
    int size = 100;
    int array[size];
    array[0] = 0;

    //preprocessing for Tsan, this part was not written by GPT
    for(int i = 0; i < size; i++){
        array[i] = 30;
    }

    #pragma omp parallel for
    //#pragma drd
    for (int i = 0; i < size; i++) {
        if (flag) {
            array[i] = array[0];
        } else {
            array[0] = array[i];
        }
    }
}

void GPTO1_WAR3(){
    int size = 100;
    int array[size];
    array[0] = 0;

    #pragma omp parallel for
    #pragma drd
    for (int i = 0; i < size; i++) {
        for (int j = 0; j < size; j++) {
            array[j] = array[i] + j;
        }
    }

}





int main(int argc, char *argv[]){
    //NAS_cg();
    //loop();
    //GPTO1_WAR1();
    //GPTO1_WARCNTRL1(10);
    //GPTO1_WARCNTRL2(1);
    //GPTO1_WAR2();
    GPTO1_WAR3();
    return 0;
}