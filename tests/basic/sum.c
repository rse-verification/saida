/* run.config
   LOG: @PTEST_NAME@.out.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-out=@PTEST_NAME@.out.c
*/

int g1, g2;

int sum(int n) {
  if (n <= 0) {
    return 0;
  }
  return sum(n-1) + n;
}


/*@
  requires 0 <= g1 <= 5;
  ensures g2 <= 15;
*/
void main() {
  g2 = sum(g1);
}
