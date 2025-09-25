/* run.config
   OPT: -saida
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
//  assume(0 <= g1 && g1 <= 5);
  g2 = sum(g1);
//  assert(g2 <= 15);
}
