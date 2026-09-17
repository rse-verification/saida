/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  This test checks that \old predicates are translated into a
  TriCera-parsable harness. Its entry-point postcondition follows directly
  from the precondition, so it does not constrain the helper result.
 */
 
int g;

int add_one(int x) {
  return x+1;
}

/*@
  requires 100 >= g >= 0;
  ensures \old(g >= 0);
*/
void main() {
  g = add_one(g);
  g = add_one(g);
}
