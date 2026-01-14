/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main="start" -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  TODO: Not supported yet.
  Tests harness generation for nested structs containing model fields
  in the return value. This is not supported and should generate
  output indicating this.
 */

struct Si {
  int x;
};

struct So start(void) {  return id(g_s);
}
void main()
{


  //The requires-clauses translated into assumes
  assume(g_s.inner.x >= 0);

  //Function call that the harness function verifies
  struct So start_result = start();

  //The ensures-clauses translated into asserts
  assert(start_result.inner<TModel offset not supported: y> == g_s.inner<TModel offset not supported: y>);
}
