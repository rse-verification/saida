/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main=start -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  Tests harness generation with a base funtion with arguments.

  This currently (2025-10-15) breaks because we need an outer
  and an inner harness function to make sure that "old" values
  exists for the arguments.
 */

struct S {
  int x;
  int y;
};


/*@contract@*/
int f_with_arg(struct S *s) {
  return s->x;
}


int start(struct S *s) {  return f_with_arg(s);
}
void main()
{
  //Declare the paramters of the function to be called
  struct S * s;


  //The requires-clauses translated into assumes
  assume((s->x >= 0));

  //Function call that the harness function verifies
  int start_result = start(s);

  //The ensures-clauses translated into asserts
  assert((start_result == $at("Old", (int)(s->x))));
}
