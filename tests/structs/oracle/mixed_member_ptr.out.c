/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  Tests harness generation for nested structs in requires/ensures
  clauses is handled correctly.
 */

struct Si {
  int x;
};

struct So {
  struct Si* inner;
};

struct Si inner;
struct So s = { &inner };


/*@
  requires \true;
  ensures inner == \old(inner);
*/
int select_inner_x(struct So structs) {
  return structs.inner->x ;
}

/*@
  requires s.inner->x >=0;
  ensures \result == s.inner->x ;
*/ 
int main(void) {
  return select_inner_x(s);
}
