/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main="start" -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  Tests harness generation for structs containing model fields.
  This is not supported and should generate output indicating this.
 */

struct S {
  int x;
};
/*@ model struct S { int y }; */

struct S g_s;

struct S id(struct S s) {
  return s;
}

/*@
  requires g_s.y >=0;
  ensures \result.y == g_s.y ;
*/ 
struct S start(void) {
  return id(g_s);
}
