/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main=func -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  Tests harness generation of boolean constants in requires/ensures clauses.
*/


int func(char a) {  return a;
}
void main()
{
  //Declare the paramters of the function to be called
  int a;


  //The requires-clauses translated into assumes
  assume(((a != 0) == 1));

  //Function call that the harness function verifies
  int func_result = func(a);

  //The ensures-clauses translated into asserts
  assert((func_result == $at(Old, (char)(a))));
}
