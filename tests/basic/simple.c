/* run.config
   LOG: @PTEST_NAME@.out.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-out=@PTEST_NAME@.out.c
*/
/*
  This test makes sure that \old terms are translated correctly.
*/
typedef int Integer;
Integer g;

Integer add_one(Integer x) {
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
