/* run.config
   LOG: @PTEST_NAME@.out.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-out=@PTEST_NAME@.out.c
*/
/*
  This test makes sure that \old terms are translated correctly.
*/
int g;

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
