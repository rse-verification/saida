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


/*@contract@*/
int select_inner_x(struct So structs) {
  return structs.inner->x ;
}


int main2(void) {
  return select_inner_x(s);
}
void main()
{
  
  
  //The requires-clauses translated into assumes
  assume((s.inner)->x >= 0);
  
  //Function call that the harness function verifies
  int main_result = main2();
  
  //The ensures-clauses translated into asserts
  assert(main_result == (s.inner)->x);
  
}
