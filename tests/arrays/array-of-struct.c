/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  Tests that access of struct member values of array elements
  in ensures clauses is handled correctly.

  TODO: TriCera v0.5 does not reconstruct the result relation for this case;
  the oracle records that current limitation.
 */

struct S {
  int x;
  int y;
};

struct S s[3];

int select_1_x(struct S structs[]) {
  return structs[1].x ;
}

/*@
  requires s[1].x >=0;
  ensures \result == s[1].x ;
*/ 
int main(void) {
  return select_1_x(s);
}
