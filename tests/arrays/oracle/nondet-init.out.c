/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main=func -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  Tests that nondeterministically initialized arrays are translated correctly.
  NOTE: This program seems to expose a bug in TriCera, the generated contract is too weak.
 */
int a[3];

/*@
  requires n == 1;
  ensures \old(n) == 1 && a == \old(a);
*/
void increment(int x[], unsigned n) {
  x[n] += 1;
}

/*@
  // requires \valid(a+1);
  assigns a[1];
  ensures a[1] == \old(a[1]) + 1;
*/
void func() {
  increment(a, 1);
}
