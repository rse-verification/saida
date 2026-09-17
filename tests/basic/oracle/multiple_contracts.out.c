/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  This test makes sure that correct contracts are considered and/or discarded.
*/
int g;

/*@
  requires -500 <= x <= 500;
  ensures \result == x+1;
*/
/*@
  requires g == x && 101 >= x && x >= 0;
  ensures \result - \old(x) == 1 && 101 >= g && g >= 0 && 101 >= \old(g) && \old(g) >= 0 && 101 >= \old(x) && \old(x) >= 0;
*/
int add_one(int x) {
  return x+1;
}

/*@
  requires 100 >= g >= 0;
  ensures g == \old(g)+2;
*/
void main() {
  g = add_one(g);
  g = add_one(g);
}
