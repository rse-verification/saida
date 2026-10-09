/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   LOG: saida_result_@PTEST_NAME@.c
   OPT: -lib-entry -main bar -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/* Control: the typedef is already available at the first declaration. */
typedef int UserInt;
extern int identity(int value);

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
