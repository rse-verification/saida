/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main=func -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  Tests that nondeterministically initialized arrays are translated correctly.

  TODO: TriCera v0.5 does not reconstruct the updated array element;
  the oracle records that current limitation.
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
