
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

/*@contract@*/
int select_inner_x(struct So *s) {
  return s->inner->x ;
}


int main(void) {
  return select_inner_x(p);
}
int saida_harness_main_inner()
{
  
  //The requires-clauses translated into assumes
  assume((p->inner)->x >= 0);
  
  //Function call that the harness function verifies
  int main_result = main();
  
  //The ensures-clauses translated into asserts
  assert(main_result == (p->inner)->x);
  
}
void saida_harness_main()
{
  
  //Call inner harness function
  saida_harness_main_inner();
  
  
}
