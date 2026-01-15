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


//No inferred contract found for step_towards_0
int step_towards_0(int x) {
    return (x < 0 
            ? x+1
            : (x > 0 
               ? x-1
               : x));
}

/*@
  assigns g_x;
  behavior gt0:
    assumes g_x > 0;
    ensures g_x == \old(g_x)-1;
  behavior lt0:
    assumes g_x < 0;
    ensures g_x == \old(g_x)+1;
  behavior eq0:
    assumes g_x == 0;
    ensures g_x == 0;
*/
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
