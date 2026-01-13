/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  Tests that access of struct member values of array elements
  in ensures clauses is handled correctly.
 */

struct S {
  int x;
  int y;
};

struct S s[3];

/*@contract@*/
int select_1_x(struct S structs[]) {
  return structs[1].x ;
}


int main2(void) {
  return select_1_x(s);
}
void main()
{


  //The requires-clauses translated into assumes
  assume(s[1].x >= 0);

  //Function call that the harness function verifies
  int main_result = main2();

  //The ensures-clauses translated into asserts
  assert(main_result == s[1].x);
}
