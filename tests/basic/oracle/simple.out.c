/* run.config
   LOG: @PTEST_NAME@.out.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-out=@PTEST_NAME@.out.c
*/

int g;

/*@
  requires g == x && x >= 0;
  ensures \old(x) - \result == -1 && g - \result == -1 && \old(g) - \result == -1 && \result >= 1;
*/
int add_one(int x) {
  return x+1;
}

/*@
  requires g >= 0;
  ensures g >= 2;
*/
void main() {
  g = add_one(g);
  g = add_one(g);
}
