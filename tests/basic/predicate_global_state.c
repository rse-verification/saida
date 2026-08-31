/* run.config
   EXIT: 1
   OPT: -lib-entry -main=entry -saida -saida-tricera-path=/definitely/not/tricera
*/

int floor_value;

/*@ predicate above_floor(integer value) = value >= floor_value; */

/*@ requires above_floor(input); */
int entry(int input)
{
  return input;
}
