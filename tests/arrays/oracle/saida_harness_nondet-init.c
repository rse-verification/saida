/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main=func -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  Tests that nondeterministically initialized arrays are translated correctly.
 */
int a[3];

/*@contract@*/
void increment(int x[], unsigned n) {
  x[n] += 1;
}


void func() {  increment(a, 1);
}
void main()
{



  //Function call that the harness function verifies
  func();

  //The ensures-clauses translated into asserts
  assert((a[1] == ($at("Old", (int)(a[1])) + 1)));
}
