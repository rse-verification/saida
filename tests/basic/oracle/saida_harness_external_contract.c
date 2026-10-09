/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   LOG: saida_result_@PTEST_NAME@.c
   OPT: -lib-entry -main bar -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/* Reproducer from https://github.com/rse-verification/saida/issues/46. */
int a;

/*@ requires a >= 0;
    requires a < 1000;
    ensures a == \old(a) + 1; */
extern void foo(void);



extern void foo();


void bar() {
    foo();
}
void saida_harness_bar_inner()
{
  
  //The requires-clauses translated into assumes
  assume(a >= 0);
  assume(a < 1000);
  
  //Function call that the harness function verifies
  bar();
  
  //The ensures-clauses translated into asserts
  assert(a == $at("Old", (int)(a)) + 1);
  
}
void saida_harness_bar()
{
  
  //Call inner harness function
  saida_harness_bar_inner();
  
  
}
