/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   LOG: saida_result_@PTEST_NAME@.c
   OPT: -lib-entry -main bar -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/* A merged prototype must not precede the type from its later declaration. */
extern int identity(int value);
typedef int UserInt;

/*@ requires value == 1;
    ensures \result == value;
*/
extern UserInt identity(UserInt value);

/*@ requires value == 1;
    ensures \result == 1;
*/
int bar(int value) {
    return identity(value);
}
