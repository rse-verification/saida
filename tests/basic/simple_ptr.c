/* run.config
   LOG: @PTEST_NAME@.out.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-out=@PTEST_NAME@.out.c
*/
/*
  TODO: Not supported yet.
  This test currently (2025-10-08) fails because \valid is not supported.
  The corresponding option to tricera is -valid-deref and works on the complete
  program level. Hence, to translate this we should remove the \valid predicate
  and add the -valid-deref option to tricera.
*/

int a;
int *g = &a;

int add_one(int *x) {
  return *x+1;
}

/*@
  requires \valid(g) && 100 >= *g >= 0;
  ensures *g == \old(*g)+2;
*/
void main() {
  *g = add_one(g);
  *g = add_one(g);
}
