/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/

/*
  Tests translation of ternary expressions for predicates.
*/

int t;


int main(void) {
    return 0;
}
int saida_harness_main_inner()
{
  
  
  //Function call that the harness function verifies
  int main_result = main();
  
  //The ensures-clauses translated into asserts
  assert($at("Old", (int)(t)) >= 0xF0 ? 1 != 0 : 0 != 0);
  
}
void saida_harness_main()
{
  
  //Call inner harness function
  saida_harness_main_inner();
  
  
}
