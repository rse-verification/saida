/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/

/*
  Tests translation of ternary expressions for predicates.
*/

int t;

/*@
  ensures (\old(t) >= 0xF0 ? 1 : 0);
*/
int main(void) {
    return 0;
}