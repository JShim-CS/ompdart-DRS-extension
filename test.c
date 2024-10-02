
int getOne(){return 1;}

void func(){
    
    int a[1000];
    int v;
    int j = 20;
    int k = 10;
    
    #pragma drd Array=arr
    for(int i = 0; i < 1000; i++){
        if(i < 20 ){
             a[i] = a[i+1] = a[2];
        }else if(i < 40){
            if(i %3 == 0){
                if(i%6 == 0){
                }else{
                    a[i] = 30;
                }
            }
           
        }else{
            a[i] = 40;
        }

        if(i == 20)a[20] = 30;
    }
    

}