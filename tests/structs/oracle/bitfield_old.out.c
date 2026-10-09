/* run.config
   LOG: @PTEST_NAME@.out.c
   LOG: saida_harness_@PTEST_NAME@.c
   LOG: saida_result_@PTEST_NAME@.c
   OPT: -saida -saida-tricera-opts="-acsl" -saida-keep-tmp -saida-out=@PTEST_NAME@.out.c
*/

int test;

struct S {
  int pend : 1;
};

int in;
struct S bf;

int helper();

/*@ ensures in ==> \old(bf.pend) == \true;
 */
void main() {
  helper();
}
