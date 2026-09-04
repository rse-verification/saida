/* run.config
   LOG: saida_harness_@PTEST_NAME@.c
   OPT: -lib-entry -main=f -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/
/*
  A let-bound lvalue must retain an array or field offset when it is used.
*/

struct Pair {
  int value;
};

struct Pair pair;

/*@
  assigns pair.value;
  ensures \let struct_alias = pair; struct_alias.value == 3;
@*/
void f(void) {
  pair.value = 3;
}
