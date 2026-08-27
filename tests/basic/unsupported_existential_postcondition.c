/* run.config
   EXIT: 1
   OPT: -lib-entry -main=entry -saida -saida-tricera-path=/must/not/run/tri -saida-out=@PTEST_NAME@.out.c
*/

/*@
  ensures \exists integer witness; 0 < witness < 0;
*/
int entry(void)
{
  return 0;
}
