/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   LOG: saida_result_@PTEST_NAME@.c
   OPT: -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/

int test;

struct S {
  int pend : 1;
};

int in;
struct S bf;

int helper();


void main() {
  helper();
}
void saida_harness_main_inner()
{
  
  
  //Function call that the harness function verifies
  main();
  
  //The ensures-clauses translated into asserts
  assert(!(in != 0) || ($at("Old", (int)(bf.pend)) != 0) == 1);
  
}
void saida_harness_main()
{
  
  //Call inner harness function
  saida_harness_main_inner();
  
  
}
