int main()
{
    unsigned int array1[5];
    unsigned int array2[5];
    for(unsigned int i = 0; i < 5; i++) {
        array1[0] = 0;
    }
    
    array2[array1[0]] = 0;
    
    return 0;
}
