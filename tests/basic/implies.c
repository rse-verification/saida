/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main=func -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  Tests harness generation of implications.
*/

int a;

/*@
  ensures a > 0 ==> \result == a;
*/
int func() {
  return (a > 0) ? a : 0;
}
