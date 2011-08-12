int main(){
    int array[3][3]={{0,0,0},{1,1,1},{2,2,2}};

    unsigned int a, b;
    __CPROVER_assume(a < 3 && b < 3);
    array[a][a] = array[b][b];
    assert(array[a][a] >= 0);
}

