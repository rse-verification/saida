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