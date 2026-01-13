/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main=func -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  Tests harness generation of implications.
*/

int a;


int func() {  return (a > 0) ? a : 0;
}
void main()
{



  //Function call that the harness function verifies
  int func_result = func();

  //The ensures-clauses translated into asserts
  assert(!(a > 0) || func_result == a);
}
