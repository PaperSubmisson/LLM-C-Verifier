// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2025 Wang Zhen <wz@nudt.edu.cn>
//
// SPDX-License-Identifier: Apache-2.0

extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "conflict_branch4.c", 3, "reach_error"); }

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

int SIZE = 200000; 

int main()
{
	int a=0,c=0,d=0,e=0;
	int st=0;
	while(c<SIZE) {
		if (c>=SIZE)  { st = 1; }
		if(c<SIZE && st==1) { 
			a = 1;
		}
		if(a == 1){
			d = 1;
		}
		if(d == 1){
			e = 1;
		}
		c++;
		__VERIFIER_assert(e==0);
	}
	return 0;
}
