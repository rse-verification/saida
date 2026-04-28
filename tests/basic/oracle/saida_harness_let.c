/* run.config
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main=f -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  This test makes sure that \let clauses are translated properly.
  See example 2.31 in "ANSI/ISO C Specification Language  Version 1.22"
  TODO: Not yet supported.
*/

int i;
int t[10];

//@ ensures 0 <= \result <= 9;
int any(void);


void f() {
  i = any();
  t[i]++;
}
void main()
{
  
  //Logic var declarations, e.g. from \forall or \exists
  int j;
  
  
  //Function call that the harness function verifies
  f();
  
  //The ensures-clauses translated into asserts
  assert(t[i] == $at("Old", (int)(t[i])) + 1);
  
}
