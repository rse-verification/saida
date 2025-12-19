int i;
int t[10];
int *p = t;

//@ ensures 0 <= \result <= 9;
int any(void);

/*@ 
  assigns i;
  assigns *(p+\at(i,Post));
  ensures \let j = i+1; *(p+j-1) == *\old(p+j-1) + 1;
@*/
void f() {
  i = any();
  *(p+i) += 1;
}
