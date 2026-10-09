/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   LOG: saida_result_@PTEST_NAME@.c
   OPT: -lib-entry -main bar -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/* Reproducer from https://github.com/rse-verification/saida/issues/46. */
int a;

/*@ requires a >= 0;
    requires a < 1000;
    ensures a == \old(a) + 1; */
extern void foo();

/*@ requires a >= 0;
    requires a < 1000;
    ensures a == \old(a) + 1; */
void bar() {
    foo();
}
