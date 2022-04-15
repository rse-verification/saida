int g1, g2;

/* inferred contracts for sum */
/*@
  requires (g1 - n == 4 && 5 >= g1 && g1 >= 4) || (g1 - n == 3 && 5 >= g1 && g1 >= 3) || (g1 - n == 2 && 5 >= g1 && g1 >= 2) || (g1 - n == 1 && 5 >= g1 && g1 >= 1) || (g1 == n && 5 >= g1 && g1 >= 0) || (g1 == 5 && n == 0);
  ensures g2 == \old(g2) && g1 == \old(g1) && \result >= 0 && (\result != 0 || ((\old(n) - \old(g1) != -4 || (5 >= \old(g1) && \old(g1) >= 4)) && (\old(n) - \old(g1) != -3 || (5 >= \old(g1) && \old(g1) >= 3)) && (\old(n) - \old(g1) != -2 || (5 >= \old(g1) && \old(g1) >= 2)) && (\old(n) - \old(g1) != -1 || (5 >= \old(g1) && \old(g1) >= 1)) && (\old(n) != \old(g1) || (5 >= \old(g1) && \old(g1) >= 0)) && (\old(n) != 0 || \old(g1) == 5 || \old(g1) == 4 || \old(g1) == 3 || \old(g1) == 2 || \old(g1) == 1 || \old(g1) == 0) && (\old(n) - \old(g1) == -4 || \old(n) - \old(g1) == -3 || \old(n) - \old(g1) == -2 || \old(n) - \old(g1) == -1 || \old(n) == \old(g1) || \old(n) == 0))) && (\old(n) - \old(g1) != -4 || ((\result + 4*\old(g1) >= 22 || \result + 3*\old(g1) >= 22 || \result + 2*\old(g1) >= 12 || 2*\old(g1) - \result >= 8 || 0 >= \result) && (\result + 4*\old(g1) >= 22 || \result + 3*\old(g1) >= 22 || -1*\result + -2*\old(g1) >= -11 || 0 >= \result) && (\result + 4*\old(g1) >= 22 || -1*\result + -3*\old(g1) >= -21 || 0 >= \result) && (-1*\result + -4*\old(g1) >= -21 || 0 >= \result))) && (\old(n) - \old(g1) != -3 || ((\result + 3*\old(g1) >= 19 || \result + 2*\old(g1) >= 19 || 2*\old(g1) - \result >= 6 || 0 >= \result) && (\result + 3*\old(g1) >= 19 || -1*\result + -2*\old(g1) >= -18 || 0 >= \result) && (-1*\result + -3*\old(g1) >= -18 || 0 >= \result || \old(g1) >= 6) && (0 >= \result || 5 >= \old(g1)))) && (\old(n) - \old(g1) != -2 || ((\result + 2*\old(g1) >= 17 || 2*\old(g1) - \result >= 4 || 0 >= \result) && (-1*\result + -2*\old(g1) >= -16 || 0 >= \result || \old(g1) >= 6) && (0 >= \result || 5 >= \old(g1)))) && (\old(n) - \old(g1) != -1 || ((\result + \old(g1) >= 16 || \old(g1) - \result >= -5 || 0 >= \result || 0 >= \old(g1)) && (-1*\result + -1*\old(g1) >= -15 || 0 >= \result || \old(g1) >= 6 || 0 >= \old(g1)) && (0 >= \result || \old(g1) >= 1) && (0 >= \result || 5 >= \old(g1)))) && (\old(n) != \old(g1) || ((\old(g1) - \result >= -10 || 0 >= \result || \old(g1) >= 6 || -1 >= \old(g1)) && (0 >= \result || \old(g1) >= 0) && (0 >= \result || 5 >= \old(g1)))) && (\old(n) - \old(g1) == -4 || \old(n) - \old(g1) == -3 || \old(n) - \old(g1) == -2 || \old(n) - \old(g1) == -1 || \old(n) == \old(g1) || 0 >= \result);
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
void test() {
//  assume(0 <= g1 && g1 <= 5);
  g2 = sum(g1);
//  assert(g2 <= 15);
}
