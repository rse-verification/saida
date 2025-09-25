/* run.config
   OPT: -saida
*/

int g;

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
