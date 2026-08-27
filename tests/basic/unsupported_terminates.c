/* run.config
   EXIT: 1
   OPT: -lib-entry -main=entry -saida -saida-tricera-opts="-acsl" -saida-out=@PTEST_NAME@.out.c
*/

/*@
  terminates \true;
  ensures \result == value;
*/
int entry(int value)
{
  return value;
}
