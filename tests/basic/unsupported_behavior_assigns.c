/* run.config
   EXIT: 1
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-out=@PTEST_NAME@.out.c
*/

int g_x;

/*@
  behavior update:
    assigns g_x;
    ensures g_x == 0;
*/
void main(void) {
  g_x = 0;
}
