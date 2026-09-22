/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main top -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  This test makes sure that existing helper contracts are preserved in the
  TriCera input and only missing helper contracts are left as placeholders.
*/

/*@
  requires x >= 0;
  ensures \result >= 1;
*/
int f1(int x) {
  return x + 1;
}

/*@contract@*/
int f2(int x) {
  return 1;
}

int top(int x) {
  return f1(x) + f2(x);
}
int saida_harness_top_inner(int x)
{
  
  //The requires-clauses translated into assumes
  assume(x >= 0);
  
  //Function call that the harness function verifies
  int top_result = top(x);
  
  //The ensures-clauses translated into asserts
  assert(top_result >= 2);
  
}
void saida_harness_top()
{
  //Declare the paramters of the function to be called
  int x;
  
  //Call inner harness function
  saida_harness_top_inner(x);
  
  
}
