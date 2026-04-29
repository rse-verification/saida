/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/

/*
  Tests translation of behavior clauses. 
  TODO: Not supported yet.
*/

int g_x;


/*@contract@*/
int step_towards_0(int x) {
    return (x < 0 
            ? x+1
            : (x > 0 
               ? x-1
               : x));
}


/*
  The above contract should be translated like the equivalent
  one below, but it currently is not.

  assigns g_x;
  ensures 
    (\old(g_x) > 0 ==> g_x == \old(g_x)-1) && 
    (\old(g_x) < 0 ==> g_x == \old(g_x)+1) &&
    (\old(g_x) == 0 ==> g_x == 0);
*/
int main(void) {
    g_x = step_towards_0(g_x);
    return 0;
}
int saida_harness_main_inner()
{
  
  
  //Function call that the harness function verifies
  int main_result = main();
  
  //The ensures-clauses translated into asserts
  assert(g_x == 0);
  assert(g_x == $at("Old", (int)(g_x)) + 1);
  assert(g_x == $at("Old", (int)(g_x)) - 1);
  
}
void saida_harness_main()
{
  
  //Call inner harness function
  saida_harness_main_inner();
  
  
}
