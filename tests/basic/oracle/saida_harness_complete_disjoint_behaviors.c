/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main=entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/

/*@contract@*/
int helper_behavior_value(int value)
{
  if (value >= 0) {
    return 10;
  }
  return 20;
}


int entry(int value)
{
  return helper_behavior_value(value);
}
int saida_harness_entry_inner(int value)
{
  
  
  //The complete/disjoint behavior declarations translated into asserts
  assert(value >= 0 || value < 0);
  assert(!(value >= 0 && value < 0));
  
  //Function call that the harness function verifies
  int entry_result = entry(value);
  
  //The ensures-clauses translated into asserts
  assert(!$at("Old", (int)(value < 0)) || entry_result == 20);
  assert(!$at("Old", (int)(value >= 0)) || entry_result == 10);
  
}
void saida_harness_entry()
{
  //Declare the paramters of the function to be called
  int value;
  
  //Call inner harness function
  saida_harness_entry_inner(value);
  
  
}
