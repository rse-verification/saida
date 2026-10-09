/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   LOG: saida_result_@PTEST_NAME@.c
   OPT: -lib-entry -main bar -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/* A contract may be attached to a later declaration with different formals. */
int a;
extern void set(int original);


extern void set(int value);

/*@contract@*/
void helper(void) {
    set(1);
}


void bar() {
    helper();
}
/*@ ensures a == \old(value);
    assigns a;
    assigns a \from value; */
extern void set(int value);


void saida_harness_bar_inner()
{
  
  //The requires-clauses translated into assumes
  assume(a == 0);
  
  //Function call that the harness function verifies
  bar();
  
  //The ensures-clauses translated into asserts
  assert(a == 1);
  
}
void saida_harness_bar()
{
  
  //Call inner harness function
  saida_harness_bar_inner();
  
  
}
