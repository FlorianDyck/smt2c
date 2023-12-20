
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
  long long p = __VERIFIER_nondet_longlong();
  long long q = __VERIFIER_nondet_longlong();
  long long r = __VERIFIER_nondet_longlong();
  assert(!(((signed long long) (p + q)) == ((signed long long) r)));
}

