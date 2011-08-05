int printf (const char*, ...);

#define MAX_SIZE 12

int A[MAX_SIZE] = {12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1};

int insertion_sort(int array[], int size) {
  int i,j;
  int key;
  
  for(i=0;i<size;i++) {
    key = array[i];
    for (j=i-1; j>=0 && array[j]>key; j--) {
      array[j+1] = array[j];
    }
    array[j+1]=key;
  }

  return 1;
}

int print_array(int array[], int size) {
  int i;
  // needs i>=0
  for (i=0; i<size; i++) {
    printf("%d ", array[i]);
  }
  printf("\n");
}

int main() {
  print_array(A, MAX_SIZE);
  //insertion_sort(A, MAX_SIZE);
  //print_array(A, MAX_SIZE);
}
