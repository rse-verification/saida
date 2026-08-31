/*@ predicate nonnegative(integer value) = value >= 0; */
/*@ predicate valid_signal(integer value) =
      nonnegative(value) && value < 100;
*/

/*@
  requires valid_signal(value);
  assigns \nothing;

  behavior enabled:
    assumes valid_signal(flag);
    requires valid_signal(value);
    ensures valid_signal(\result);

  behavior disabled:
    assumes !valid_signal(flag);
    ensures \result == \old(value);

  complete behaviors enabled, disabled;
  disjoint behaviors enabled, disabled;
*/
int entry(int value, int flag)
{
  return value;
}
