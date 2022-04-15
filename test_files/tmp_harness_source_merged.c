int g;

/*@contract@*/
int add_one(int x) {
  return x+1;
}



void main2() {
  g = add_one(g);
  g = add_one(g);
}
extern int non_det_int();

void main()
{
  //Non-det assignment of global variables
  g = non_det_int();




  //The requires-clauses translated into assumes
  assume((g >= 0));


  //Function call that the harness function verifies
  main2();

  //The ensures-clauses translated into asserts
  assert((g >= 2));
}
