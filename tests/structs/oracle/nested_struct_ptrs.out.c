
/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  Tests that access of nested struct member values of array elements
  in ensures clauses is handled correctly.
 */

struct Si {
  int x;
};

struct So {
  struct Si *inner;
};

struct Si inner;
struct So outer = { &inner };

struct So *p = &outer;

/*@
  requires \true;
  ensures \old(inner) == inner;
*/
int select_inner_x(struct So *s) {
  return s->inner->x ;
}

/*@
  requires p->inner->x >=0;
  ensures \result == p->inner->x ;
*/ 
int main(void) {
  return select_inner_x(p);
}
