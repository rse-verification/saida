/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   LOG: saida_result_@PTEST_NAME@.c
   OPT: -lib-entry -main bar -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/* A merged contract must follow its global declarations and appear once. */
extern void set(int value);
int a;

/*@ assigns a \from value;
    ensures a == value;
*/
extern void set(int value);

/*@ requires a == 0;
    ensures a == 1;
*/
void bar(void) {
    set(1);
}
