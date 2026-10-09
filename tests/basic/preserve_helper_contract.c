/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main top -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  This test makes sure that existing helper contracts are preserved in the
  TriCera input and only missing helper contracts are left as placeholders.
*/

/*@
  requires x >= 0;
  ensures \result >= 1;
*/
int f1(int x) {
  return x + 1;
}

int f2(int x) {
  return 1;
}

/*@
  requires x >= 0;
  ensures \result >= 2;
*/
int top(int x) {
  return f1(x) + f2(x);
}
