/* run.config
   EXIT: 1
   OPT: -lib-entry -main=entry -saida -saida-tricera-opts="-acsl" -saida-out=@PTEST_NAME@.out.c
*/

/*@
  behavior bounded:
    assumes value >= 0;
    check requires value <= 10;
    ensures \result == value;
*/
int entry(int value)
{
  return value;
}
