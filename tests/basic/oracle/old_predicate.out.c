/* run.config
   LOG: @PTEST_NAME@.out.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-out=@PTEST_NAME@.out.c
*/
/*
  This test makes sure that \old predicates are translated correctly.
 */
 
int g;

/*@
  requires g == x;
  ensures \old(x) - \result == -1 && g - \result == -1 && \old(g) - \result == -1;
*/
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
