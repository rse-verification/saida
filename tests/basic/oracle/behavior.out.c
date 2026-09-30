/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/

/*
  Tests translation of behavior clauses with distinct pre-state assumptions.
*/

int g_x;


/*@
  requires x == g_x;
  ensures (\old(x) != 0 || \result == 0) && (\result - \old(x) == 1 || \old(x) >= 0) && (\result - \old(x) == -1 || 0 >= \old(x));
*/
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
  one below.

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
