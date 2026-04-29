/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  TODO: Not supported yet.
  Tests harness generation for structs containing model fields.
  This is not supported and should generate output indicating this.
 */

struct S {
  int x;
};

int main(void) {
  return select_x(s);
}
int saida_harness_main_inner()
{
  
  //The requires-clauses translated into assumes
  assume(s<TModel offset not supported: y> >= 0);
  
  //Function call that the harness function verifies
  int main_result = main();
  
  //The ensures-clauses translated into asserts
  assert(main_result == s.x);
  
}
void saida_harness_main()
{
  
  //Call inner harness function
  saida_harness_main_inner();
  
  
}
