/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  This test makes sure that \old predicates are translated correctly.
 */
 
int g;

/*@contract@*/
int add_one(int x) {
  return x+1;
}


void main2() {
  g = add_one(g);
  g = add_one(g);
}
void main()
{


  //The requires-clauses translated into assumes
  assume(100 >= g && g >= 0);

  //Function call that the harness function verifies
  main2();

  //The ensures-clauses translated into asserts
  assert($at("Old", (int)(g >= 0)));
}
