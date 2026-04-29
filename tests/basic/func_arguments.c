/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main=start -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  Tests harness generation with a base funtion with arguments.
 */

struct S {
  int x;
  int y;
};


int f_with_arg(struct S *s) {
  return s->x;
}

/*@
  requires s->x >=0;
  ensures \result == \old(s->x);
*/ 
int start(struct S *s) {
  return f_with_arg(s);
}
