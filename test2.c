
int getOne(){return 1;}

void func(){
    
    int a[1000];
    int v;
    int j = 20;
    int k = 10;
    v+=j;
    #pragma drd
    for(int i = 0; i < 1000; i++){
        
       a[i] = 20;
       k = a[i+2];
    }
    v+=k;
    
  
    

}