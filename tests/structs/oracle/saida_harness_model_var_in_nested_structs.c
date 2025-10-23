/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  Tests harness generation for nested structs containing model fields.
  This is not supported and should generate output indicating this.
 */

struct Si {
  int x;
};

int main2(void) {
  return select_inner_x(s);
}
void main()
{


  //The requires-clauses translated into assumes
  assume((s.inner.Model fields not supported in structs >= 0));

  //Function call that the harness function verifies
  int main_result = main2();

  //The ensures-clauses translated into asserts
  assert((main_result == s.inner.x));
}
