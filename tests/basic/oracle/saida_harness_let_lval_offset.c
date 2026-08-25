/* run.config
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main=f -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  A let-bound lvalue must retain an array or field offset when it is used.
*/

struct Pair {
  int value;
};

struct Pair pair;


void f(void) {
  pair.value = 3;
}
void saida_harness_f_inner()
{
  //Logic var declarations, e.g. from \\forall or \\exists
  struct Pair struct_alias;
  
  
  //Function call that the harness function verifies
  f();
  
  //The ensures-clauses translated into asserts
  assert(pair.value == 3);
  
}
void saida_harness_f()
{
  
  //Call inner harness function
  saida_harness_f_inner();
  
  
}
