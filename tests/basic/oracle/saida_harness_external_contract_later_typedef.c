/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   LOG: saida_result_@PTEST_NAME@.c
   OPT: -lib-entry -main bar -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/* A merged prototype must not precede the type from its later declaration. */
extern int identity(int value);
typedef int UserInt;


extern UserInt identity(UserInt value);


int bar(int value) {
    return identity(value);
}
/*@ requires value == 1;
    ensures \result == \old(value); */
extern int identity(UserInt value);


int saida_harness_bar_inner(int value)
{
  
  //The requires-clauses translated into assumes
  assume(value == 1);
  
  //Function call that the harness function verifies
  int bar_result = bar(value);
  
  //The ensures-clauses translated into asserts
  assert(bar_result == 1);
  
}
void saida_harness_bar()
{
  //Declare the paramters of the function to be called
  int value;
  
  //Call inner harness function
  saida_harness_bar_inner(value);
  
  
}
