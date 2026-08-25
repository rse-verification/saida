/* run.config
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main=f -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  Control case: the \let binding itself is outside the label, but its body
  contains \old.  Expanding that body keeps the label around the value and is
  therefore safe for the conservative check.
*/

int value;

/*@
  assigns value;
  ensures \let old_value = \old(value); value == old_value + 1;
@*/
void f(void) {
  value++;
}
