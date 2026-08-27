/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main=entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/


int entry(void)
{
  return 0;
}
int saida_harness_entry_inner()
{
  //Logic var declarations, e.g. from \forall or \exists
  int witness;
  
  
  //Function call that the harness function verifies
  int entry_result = entry();
  
  //The ensures-clauses translated into asserts
  assert(witness == witness);
  
}
void saida_harness_entry()
{
  
  //Call inner harness function
  saida_harness_entry_inner();
  
  
}
