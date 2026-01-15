/* run.config
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  This test makes sure that \let clauses are translated properly. 
  TODO: Not yet supported.
*/

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
