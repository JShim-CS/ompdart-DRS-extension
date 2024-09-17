#include<omp.h>

void func(){
    
    int a[1000];

    #pragma drd
    for(int i = 0; i < 1000; i++){
        if(i < 20){
            if(i < 10 && i%3 == 0){
                if(i%2 == 0){
                    a[i] = i;
                }
            }
        }else if(i == 30){
            a[i*2%1000] = i*2;
        }else{
            a[i] = a[(i+40)%1000];
        }

        
    }
    
    #pragma omp target
    for(int j = 0; j < 1000; j++){
        a[j] *= j;
    }

}