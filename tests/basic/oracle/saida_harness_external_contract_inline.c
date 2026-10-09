/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   LOG: saida_result_@PTEST_NAME@.c
   OPT: -lib-entry -main bar -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/* Single-line contracts, a multiline declaration and renamed formals. */
int a;

/*@ ensures a == \old(renamed);
    assigns a;
    assigns a \from renamed; */
extern void set(int renamed);



extern void set(
    int value);
extern void set(int renamed);


void bar() {
    set(1);
}
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
