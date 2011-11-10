int main(){
    int e;
    e = bla();
    //__CPROVER_predicate(e == 1);
    //__CPROVER_predicate(e == 2);
    __CPROVER_assume(e == 1 || e == 2);
    __CPROVER_assert(!(e == 1 && e == 2), "1");
}

