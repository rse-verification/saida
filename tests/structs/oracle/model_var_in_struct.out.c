/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  TODO: Not supported yet.
  Tests harness generation for structs containing model fields.
  This is not supported and should generate output indicating this.
 */

struct S {
  int x;
};
/*@ model struct S { int y }; */

struct S s;

//No inferred contract found for select_x
int select_x(struct S structs) {
  return structs.x ;
}

/*@
  requires s.y >=0;
  ensures \result == s.x ;
*/ 
int main(void) {
  return select_x(s);
}
