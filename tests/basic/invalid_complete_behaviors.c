/* run.config
   EXIT: 1
   OPT: -lib-entry -main=entry -saida -saida-tricera-opts="-acsl" -saida-out=@PTEST_NAME@.out.c
*/

int helper_constant(int value)
{
  (void)value;
  return 10;
}

/*@
  behavior positive:
    assumes value > 0;
    ensures \result == 10;

  behavior negative:
    assumes value < 0;
    ensures \result == 10;

  complete behaviors positive, negative;
  disjoint behaviors positive, negative;
*/
int entry(int value)
{
  return helper_constant(value);
}
