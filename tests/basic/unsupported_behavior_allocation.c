/* run.config
   EXIT: 1
   OPT: -lib-entry -main=entry -saida -saida-tricera-opts="-acsl" -saida-out=@PTEST_NAME@.out.c
*/

/*@
  allocates \nothing;
  frees \nothing;
  ensures \result == value;
*/
int entry(int value)
{
  return value;
}
