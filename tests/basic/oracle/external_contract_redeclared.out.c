/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   LOG: saida_result_@PTEST_NAME@.c
   OPT: -lib-entry -main bar -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/* A contract may be attached to a later declaration with different formals. */
int a;
extern void set(int original);

/*@ assigns a \from value; ensures a == value; */
extern void set(int value);

/*@
  requires a == 0;
  ensures a == 1 && \old(a) == 0;
*/
void helper(void) {
    set(1);
}

/*@ requires a == 0; ensures a == 1; */
void bar() {
    helper();
}
