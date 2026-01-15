/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main="start" -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  TODO: Not supported yet.
  Tests harness generation for nested structs containing model fields
  in the return value. This is not supported and should generate
  output indicating this.
 */

struct Si {
  int x;
};
/*@ model struct Si { int y }; */

struct So {
  struct Si inner;
};

struct So g_s;

//No inferred contract found for id
struct So id(struct So s) {
  return s;
}

/*@
  requires g_s.inner.x >=0;
  ensures \result.inner.y == g_s.inner.y ;
*/ 
struct So start(void) {
  return id(g_s);
}
