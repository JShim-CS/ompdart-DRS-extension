
int getOne(){return 1;}

void func(){
    
    int a[1000];
    int v;
    int j = 20;
    int k = 10;
    
    #pragma drd Array=arr
    for(int i = 0; i < 1000; i++){
        a[i+2] = a[i];
    }
    

}