/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/

/*
  Tests translation of ternary expressions for terms.
*/

int t;


int main2(void) {
    return 0;
}
void main()
{
  
  
  
  //Function call that the harness function verifies
  int main_result = main2();
  
  //The ensures-clauses translated into asserts
  assert((($at("Old", (int)(t)) >= 0xF0 ? 1 : 0) != 0) == 1);
  
}
