
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
  int q = __VERIFIER_nondet_int();
  assert(!(((signed int) ((signed int) ((unsigned short) p))) == ((signed int) q)));
}

