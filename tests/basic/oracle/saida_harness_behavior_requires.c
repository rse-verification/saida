/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main=entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/

/*@contract@*/
int helper_identity(int value)
{
  return value;
}


int entry(int value)
{
  return helper_identity(value);
}
int saida_harness_entry_inner(int value)
{
  
  //The requires-clauses translated into assumes
  assume(-100 <= value && value <= 100);
  
  //The complete/disjoint behavior declarations translated into asserts
  assert(value >= 0 || value < 0);
  assert(!(value >= 0 && value < 0));
  
  //Behavior-specific requires translated into conditional assumes
  assume(!(value < 0) || value >= -10);
  assume(!(value >= 0) || value <= 10);
  
  //Function call that the harness function verifies
  int entry_result = entry(value);
  
  //The ensures-clauses translated into asserts
  assert(!$at("Old", (int)(value < 0)) || entry_result == $at("Old", (int)(value)));
  assert(!$at("Old", (int)(value >= 0)) || entry_result == $at("Old", (int)(value)));
  
}
void saida_harness_entry()
{
  //Declare the paramters of the function to be called
  int value;
  
  //Call inner harness function
  saida_harness_entry_inner(value);
  
  
}
