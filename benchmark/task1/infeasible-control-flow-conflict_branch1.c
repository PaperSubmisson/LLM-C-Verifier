// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2025 Wang Zhen <wz@nudt.edu.cn>
//
// SPDX-License-Identifier: Apache-2.0

extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "conflict_branch1.c", 3, "reach_error"); }

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
int __VERIFIER_nondet_int();

int SIZE=200000000;

int main() {
  int x = 10;
  while (x < SIZE) {
    int tmp = __VERIFIER_nondet_int();
    if (tmp < 100)    { x--; }
    if (tmp > 900)    { x--; }
    x++;
  __VERIFIER_assert(x>=0);
  }
  return 0;
}
