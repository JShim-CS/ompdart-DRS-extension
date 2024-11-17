int main(){
/*--------------------------------------------------------------------
c     now change the sign of the forcing function, 
c-------------------------------------------------------------------*/
int grid_points[10];
int i,j,k,m;
int forcing[100][100][100][100];
#pragma drd  
  for (i = 1; i < grid_points[0]-1; i++) {
    for (j = 1; j < grid_points[1]-1; j++) {
      for (k = 1; k < grid_points[2]-1; k++) {
	for (m = 0; m < 5; m++) {
	  forcing[i][j][k][m] = -1.0 * forcing[i+1][j][k][m];
	}
      }
    }
  }
  return 0;
}

