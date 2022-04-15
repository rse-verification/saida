int g;

/*@
  requires x == g && g >= 0;
  ensures \result - \old(g) == 1 && g == \old(g) && \old(x) == \old(g) && \old(g) >= 0;
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
