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
  requires value == 0;

  behavior nonpositive:
    assumes value <= 0;
    requires value < 0;
    ensures \result == 10;

  behavior nonnegative:
    assumes value >= 0;
    ensures \result == 10;

  disjoint behaviors nonpositive, nonnegative;
*/
int entry(int value)
{
  return helper_constant(value);
}
