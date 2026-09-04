/* run.config
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main=f -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  A post-state \let binding must not be expanded inside \old.  The binding
  below is outside the label, so Saida must reject it rather than silently
  changing the state of the array index used by \old.
*/

int index;
int values[2];

/*@
  assigns index, values[0..1];
  ensures \let post_index = index; \old(values[post_index]) == 0;
@*/
void f(void) {
  index = 1;
  values[1] = 1;
}
