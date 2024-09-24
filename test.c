

void func(){
    
    int a[1000];

    #pragma drd
    for(int i = 0; i < 1000; i++){
        if(i < 20 ){
            if(i%2 == 0){
                a[i] = 10;
            }else if(i%2 == 1){
                a[i] = 15;
            }else{
                a[i] = 16;
            }
        }else if(i < 40){
            a[i] = 30;
        }else{
            a[i] = 40;
        }
    }
    
    #pragma omp target
    for(int j = 0; j < 1000; j++){
        a[j] *= j;
    }

}