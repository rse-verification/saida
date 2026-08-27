/* run.config
   EXIT: 1
   OPT: -lib-entry -main=entry -saida -saida-tricera-path=/must/not/run/tri -saida-out=@PTEST_NAME@.out.c
*/

/*@
  requires \forall integer witness; witness == witness;
  ensures \result == value;
*/
int entry(int value)
{
  return value;
}
