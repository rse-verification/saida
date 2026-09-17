/* run.config
   BIN: @PTEST_NAME@.out.c
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-out=@PTEST_NAME@.out.c
   DEPS: @PTEST_NAME@.out.c
   EXECNOW: LOG @PTEST_NAME@.parse.log grep -q "contract for sum" @PTEST_NAME@.out.c && @frama-c-cmd@ @PTEST_NAME@.out.c > @PTEST_NAME@.parse.log
*/

/* TriCera may reconstruct semantically equivalent recursive contracts with
   different syntax. The ptest checks that a contract was produced and that
   the generated output is valid Frama-C input, rather than snapshotting the
   solver-specific formula. */

int g1, g2;

int sum(int n) {
  if (n <= 0) {
    return 0;
  }
  return sum(n-1) + n;
}


/*@
  requires 0 <= g1 <= 5;
  ensures g2 <= 15;
*/
void main() {
  g2 = sum(g1);
}
