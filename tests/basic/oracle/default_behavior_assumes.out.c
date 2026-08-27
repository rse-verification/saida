/* run.config
   LOG: @PTEST_NAME@.out.c
   BIN: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
   DEPS: saida_harness_@PTEST_NAME@.c
   EXECNOW: LOG saida_harness_@PTEST_NAME@.normalized.c sed 's/[[:space:]]*$//' saida_harness_@PTEST_NAME@.c > saida_harness_@PTEST_NAME@.normalized.c
*/

int g_x;

/*@
  behavior default:
    assumes g_x >= 0;
    ensures g_x >= 0;
*/
int main(void) {
  return g_x;
}
