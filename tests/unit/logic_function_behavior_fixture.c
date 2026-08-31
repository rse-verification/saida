/*@ logic integer increment(integer value) = value + 1; */

/*@
  requires increment(value) > 0;
  requires value < 2147483647;
  assigns \nothing;

  behavior enabled:
    assumes increment(flag) > 0;
    requires increment(value) > 0;
    ensures \result == increment(\old(value));

  behavior disabled:
    assumes increment(flag) <= 0;
    ensures \result == \old(value);

  complete behaviors enabled, disabled;
  disjoint behaviors enabled, disabled;
*/
int entry(int value, int flag)
{
  return flag >= 0 ? value + 1 : value;
}
