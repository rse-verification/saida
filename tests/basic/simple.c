/* run.config
   LOG: @PTEST_NAME@.out.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-out=@PTEST_NAME@.out.c
*/

int g;

int add_one(int x) {
  return x+1;
}

/*@
  requires 100 >= g >= 0;
  ensures g >= \old(g)+2;
*/
void main() {
  g = add_one(g);
  g = add_one(g);
}
