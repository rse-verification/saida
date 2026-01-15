/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  TODO: Not supported yet.
  Tests harness generation for nested structs containing model fields.
  This is not supported and should generate output indicating this.
 */

struct Si {
  int x;
};
/*@ model struct Si { int y }; */

struct So {
  struct Si inner;
};

struct So s;

//No inferred contract found for select_inner_x
int select_inner_x(struct So structs) {
  return structs.inner.x ;
}

/*@
  requires s.inner.y >=0;
  ensures \result == s.inner.x ;
*/ 
int main(void) {
  return select_inner_x(s);
}
