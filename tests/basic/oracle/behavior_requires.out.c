/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main=entry -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/

/*@
  requires 10 >= value && value >= -10;
  ensures \old(value) == \result && 10 >= \result && \result >= -10;
*/
int helper_identity(int value)
{
  return value;
}

/*@
  requires -100 <= value <= 100;

  behavior nonnegative:
    assumes value >= 0;
    requires value <= 10;
    ensures \result == value;

  behavior negative:
    assumes value < 0;
    requires value >= -10;
    ensures \result == value;

  complete behaviors nonnegative, negative;
  disjoint behaviors nonnegative, negative;
*/
int entry(int value)
{
  return helper_identity(value);
}
