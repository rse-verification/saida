/* run.config
   LOG: @PTEST_NAME@.out.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-out=@PTEST_NAME@.out.c
*/

int g1, g2;

/*@
  requires g1 >= n && n >= 0 && 5 >= g1;
  ensures g2 == \old(g2) && g1 == \old(g1) && 15 >= \result && \result >= 0 && 5 >= \old(n) && \old(n) >= 0 && 5 >= \old(g1) && \old(g1) >= 0 && (\old(n) == \old(g1) || \old(g1) - \old(n) >= 2 || (-1*\result + -1*\old(g1) >= -15 && 10 >= \result)) && (\old(n) - \old(g1) >= -1 || (\result - \old(g1) == -5 && \old(n) - \old(g1) == -5) || (\old(n) - \old(g1) == -4 && -1*\result + -4*\old(g1) >= -21 && -1*\result + -3*\old(g1) >= -21 && -1*\result + -2*\old(g1) >= -11 && \old(g1) - \result >= 3) || (\old(n) - \old(g1) == -3 && -1*\result + -3*\old(g1) >= -18 && -1*\result + -2*\old(g1) >= -13 && \old(g1) - \result >= 2) || (\old(n) - \old(g1) == -2 && -1*\result + -2*\old(g1) >= -16 && 6 >= \result));
*/
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
