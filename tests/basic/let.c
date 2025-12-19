int i;
int t[10];

//@ ensures 0 <= \result <= 9;
int any(void);

/*@ 
  assigns i;
  assigns t[\at(i,Post)];
  ensures \let j = i; t[j] == \old(t[j]) + 1;
@*/
void f() {
  i = any();
  t[i]++;
}
