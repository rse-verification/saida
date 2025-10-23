/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main="start" -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  Tests harness generation for structs containing model fields.
  This is not supported and should generate output indicating this.
 */

struct S {
  int x;
};

struct S start(void) {  return id(g_s);
}
void main()
{


  //The requires-clauses translated into assumes
  assume((model-field not supported in lval >= 0));

  //Function call that the harness function verifies
  struct S start_result = start();

  //The ensures-clauses translated into asserts
  assert((model-field not supported in return == model-field not supported in lval));
}
