
int getOne(){return 1;}

void func(){
    
    int a[1000];
    int v;
    int j = 20;
    int k = 10;
    v+=j;
    #pragma drd
    for(int i = 0; i < 1000; i++){
        if(a[i+2] = 0){
            a[i] = a[i+3];
        }

        //double negation not allowed
        if((i%2 != 0)){
            a[i+5] = 10;
        }
        
       
    }
    v+=k;
    
  
    

}