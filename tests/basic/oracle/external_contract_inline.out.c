/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   LOG: saida_result_@PTEST_NAME@.c
   OPT: -lib-entry -main bar -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/* Single-line contracts, a multiline declaration and renamed formals. */
int a;

/*@ assigns a \from value; ensures a == value; */
extern void set(
    int value);
extern void set(int renamed);

/*@ requires a == 0; ensures a == 1; */
void bar() {
    set(1);
}
