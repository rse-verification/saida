/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/

int g_x;


int main(void) {
  return g_x;
}
int saida_harness_main_inner()
{


  //Function call that the harness function verifies
  int main_result = main();

  //The ensures-clauses translated into asserts
  assert(!$at("Old", (int)(g_x >= 0)) || g_x >= 0);

}
void saida_harness_main()
{

  //Call inner harness function
  saida_harness_main_inner();


}
