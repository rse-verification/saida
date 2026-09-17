/* run.config
   OPT: -lib-entry -saida -saida-tricera-opts="-acsl" -saida-out=@DEV_NULL@
*/

/*
  Smoke-test recursive inference. TriCera may infer equivalent postconditions
  in different textual forms, so this test checks successful execution rather
  than comparing a solver-dependent contract oracle.
*/

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
