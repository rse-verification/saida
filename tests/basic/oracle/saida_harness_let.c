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


/*@contract@*/
void f() {
  i = any();
  t[i]++;
}
void main()
{

  //printing logic var declarations, e.g. from \forall or \exists
  int j;


  //Function call that the harness function verifies
  f();

  //The ensures-clauses translated into asserts
  assert(t[i] == $at("Old", (int)(t[i])) + 1);
}
