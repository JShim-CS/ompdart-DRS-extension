

void func(){
    
    int a[1000];
    int v;
    int j = 0;
    #pragma drd
    for(int i = 0; i < 1000; i++){
        if(i < 20 ){
             if(i%2 == 0 && j){
                a[i] = 10;
                v += 10;
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
    
    #pragma omp target map(to:a)
    for(int j = 0; j < 1000; j++){
        a[j] *= j;
    }

}