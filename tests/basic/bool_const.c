/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main=func -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  Tests harness generation of boolean constants in requires/ensures clauses.
*/

/*@
  requires a == \true;
  ensures \result == a;
*/
int func(char a) {
  return a;
}
