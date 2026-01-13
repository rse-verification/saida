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
  assume(g_s<TModel offset not supported: y> >= 0);

  //Function call that the harness function verifies
  struct S start_result = start();

  //The ensures-clauses translated into asserts
  assert(start_result<TModel offset not supported: y> == g_s<TModel offset not supported: y>);
}
