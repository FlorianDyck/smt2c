
extern char __VERIFIER_nondet_char();
extern short __VERIFIER_nondet_short();
extern int __VERIFIER_nondet_int();
extern long __VERIFIER_nondet_longlong();
extern void reach_error();
void assert (int assertion) {
    if(!assertion) {
        reach_error();
    }
}
int main()
{
  char p = __VERIFIER_nondet_char();
  char q = __VERIFIER_nondet_char();
  char r = __VERIFIER_nondet_char();
  assert(!(((signed char) (p + q)) == ((signed char) r)));
}

