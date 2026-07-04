// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2025 Wang Zhen <wz@nudt.edu.cn>
//
// SPDX-License-Identifier: Apache-2.0

extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "unreach_branch5.c", 3, "reach_error"); }
extern _Bool __VERIFIER_nondet_bool(void);

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
int __VERIFIER_nondet_int();

int SIZE=200000000;

int main() {
  int a=10;
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();

  while (a < SIZE) {
    if (x>y && x<y) {
      a--;
    }
    else{
      a++;
    }
  }
  __VERIFIER_assert(a>=0);
  return 0;
}

