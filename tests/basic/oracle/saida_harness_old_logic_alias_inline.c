/* run.config
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main=f -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  Control case: the \let binding itself is outside the label, but its body
  contains \old.  Expanding that body keeps the label around the value and is
  therefore safe for the conservative check.
*/

int value;


void f(void) {
  value++;
}
void saida_harness_f_inner()
{
  //Logic var declarations, e.g. from \forall or \exists
  int old_value;
  
  
  //Function call that the harness function verifies
  f();
  
  //The ensures-clauses translated into asserts
  assert(value == $at("Old", (int)(value)) + 1);
  
}
void saida_harness_f()
{
  
  //Call inner harness function
  saida_harness_f_inner();
  
  
}
