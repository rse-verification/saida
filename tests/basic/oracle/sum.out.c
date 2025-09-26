/* run.config
   LOG: @PTEST_NAME@.out.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-out=@PTEST_NAME@.out.c
*/

int g1, g2;

/*@
  requires g1 >= n && n >= 0 && 5 >= g1;
  ensures \old(g1) == g1 && \old(g2) == g2 && 5 >= \old(n) && \old(n) >= 0 && \result >= 0 && 5 >= g1 && g1 >= 0 && (\old(n) - g1 != -4 || ((g1 != 4 || ((\result >= 6 || 3 >= \result) && (\result >= 4 || 0 >= \result))) && (-1*\result + -4*g1 >= -21 || 0 >= \result || 3 >= g1))) && (\old(n) - g1 != -3 || 0 >= \result || 2 >= g1 || (-1*\result + -3*g1 >= -18 && (\result + 2*g1 >= 19 || 2*g1 - \result >= 6))) && (\old(n) - g1 != -2 || 0 >= \result || 1 >= g1 || (-1*\result + -2*g1 >= -16 && 2*g1 - \result >= 4)) && (\old(n) - g1 != -1 || 0 >= \result || 0 >= g1 || (-1*\result + -1*g1 >= -15 && g1 - \result >= -5)) && (\old(n) != g1 || (15 >= \result && (g1 - \result >= -10 || 0 >= \result))) && (\result != 0 || g1 >= \old(n) || 0 >= \old(n)) && (\old(n) - g1 == -4 || \old(n) - g1 == -3 || \old(n) - g1 == -2 || \old(n) - g1 == -1 || \old(n) == g1 || 0 >= \result);
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
//  assume(0 <= g1 && g1 <= 5);
  g2 = sum(g1);
//  assert(g2 <= 15);
}
