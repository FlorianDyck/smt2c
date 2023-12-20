
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
  short p = __VERIFIER_nondet_short();
  short q = __VERIFIER_nondet_short();
  short r = __VERIFIER_nondet_short();
  assert(!(((signed short) ((((p >> 15) ? (0xFFFF) : (0)) >> ((q < 16) ? (q) : (0))) | ((q >= 16) ? (0) : (p >> q)))) == ((signed short) r)));
}

