/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main=entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/

int helper_behavior_value(int value)
{
  if (value >= 0) {
    return 10;
  }
  return 20;
}

/*@
  assigns \nothing;

  behavior nonnegative:
    assumes value >= 0;
    ensures \result == 10;

  behavior negative:
    assumes value < 0;
    ensures \result == 20;

  complete behaviors nonnegative, negative;
  disjoint behaviors nonnegative, negative;
*/
int entry(int value)
{
  return helper_behavior_value(value);
}
