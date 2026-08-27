/* run.config
   EXIT: 1
   OPT: -lib-entry -main=entry -saida -saida-tricera-path=/must/not/run/tri -saida-out=@PTEST_NAME@.out.c
*/

/*@
  requires value == 0 || (\exists integer witness; witness == value);
  ensures \result == value;
*/
int entry(int value)
{
  return value;
}
