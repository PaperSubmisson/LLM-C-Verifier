import re
import json
from pycparser import c_generator, c_ast, c_parser

def parse_boogie_model(model_text):
    data = {}
    
    array_definitions = {} 
    
    array_references = {}

    lines = model_text.splitlines()
    i = 0
    
    def clean_val(val):
        val = val.strip()
        
        m_neg = re.match(r'\(\-\s+([0-9\.]+)\)', val)
        if m_neg:
            return f"-{m_neg.group(1)}"
            
        
        m_frac = re.match(r'\(\/\s+([0-9\.]+)\s+([0-9\.]+)\)', val)
        if m_frac:
            
            return f"({m_frac.group(1)} / {m_frac.group(2)})"
            
        
        m_neg_frac = re.match(r'\(\-\s+\(\/\s+([0-9\.]+)\s+([0-9\.]+)\)\)', val)
        if m_neg_frac:
            return f"(-{m_neg_frac.group(1)} / {m_neg_frac.group(2)})"

        return val

    while i < len(lines):
        line = lines[i].strip()
        i += 1
        if not line: continue
        if "END_MODEL" in line: break
        
        if line.startswith("***") or line.startswith("tickleBool"):
            continue

        if "-> {" in line:
            parts = line.split("-> {")
            key = parts[0].strip()
            
            if key == "ControlFlow":
                while i < len(lines) and "}" not in lines[i]:
                    i += 1
                i += 1 
                continue
            
            block_data = {}
            while i < len(lines):
                sub_line = lines[i].strip()
                i += 1
                if sub_line == "}":
                    break
                
                if "->" in sub_line:
                    k_v = sub_line.split("->")
                    idx = clean_val(k_v[0])
                    val = clean_val(k_v[1])
                    block_data[idx] = val
            
            array_definitions[key] = block_data

        elif "->" in line:
            parts = line.split("->")
            key = parts[0].strip()
            val = parts[1].strip()
            
            if not val: 
                continue
                
            match_array = re.search(r'\(as-array\)\s+\(([^\)]+)\)', val)
            if match_array:
                ref_name = match_array.group(1) 
                array_references[key] = ref_name
            else:
                data[key] = clean_val(val)

    for var_name, ref_name in array_references.items():
        if ref_name in array_definitions:
            arr_data = array_definitions[ref_name]
            display_name = var_name.split('@')[0]
            display_name = re.sub(r'^snap_loop\d+_(?:entry|head|body|done)_', '', display_name)
            display_name = re.sub(r'^snap_loop_\d+_(?:call|called)_', '', display_name)
            display_name = re.sub(r'^snap_assertion\d+_', '', display_name)
            display_name = re.sub(r'^snap_\w+_(?:entry|exit)_', '', display_name)
            display_name = re.sub(r'^snap_call_\d+_(?:pre|post)_', '', display_name)
            
            desc_parts = []
            default_val = None
            
            for idx, val in arr_data.items():
                if idx == "else":
                    default_val = val
                else:
                    desc_parts.append(f"{display_name}[{idx}]={val}")
            
            if default_val is not None:
                desc_parts.append(f"{display_name}[others]={default_val}")
                
            data[var_name] = ", ".join(desc_parts)
        else:
            data[var_name] = "Unknown Array"

    return data

class InstrumentingGenerator(c_generator.CGenerator):
    def __init__(self, model_data):
        super().__init__()
        self.model_data = model_data
        self.tmp_count = 0 

    def _get_boogie_temp_val(self):
        temp_name = f"snap_nondet_{self.tmp_count}"
        self.tmp_count += 1 
        for key, val in self.model_data.items():
            if "@" in key:
                if key.startswith(temp_name):
                    return val
        
        return "0"

    def visit_FuncDef(self, node):
        func_name = node.decl.name
        if func_name in ["__VERIFIER_assert","reach_error"]:
            return ""
        return super().visit_FuncDef(node)
  
    def visit_FuncCall(self, node):
        
        func_name = ""
        if isinstance(node.name, c_ast.ID):
            func_name = node.name.name

        if func_name in ["__VERIFIER_nondet_int","__VERIFIER_nondet_uint"]:
            return self._get_boogie_temp_val()
        
        if func_name == "reach_error":
            s = f'  printf(" Assertion failed \\n");\n'
            s += '  exit(1);\n'
            return s

        if func_name in ["__VERIFIER_assert", "___SL_ASSERT"]:
           
            cond = self.visit(node.args.exprs[0])
            
            s = f'if (!({cond})) {{\n'
            s += f'  printf(" Assertion failed");\n'
            s += '  exit(1);\n'
            s += '}'
            return s
            
        return super().visit_FuncCall(node)

class RandomInputGenerator(c_generator.CGenerator):
    def __init__(self):
        super().__init__()
        self.blacklisted_funcs = [
            "malloc", "calloc", "free", "alloca", "realloc",
            "reach_error", 
            "__VERIFIER_assert",
            "___SL_ASSERT", 
            "assume_abort_if_not",
            "__VERIFIER_nondet_int",
            "__VERIFIER_nondet_uint",
            "__VERIFIER_nondet_bool",
            "__VERIFIER_nondet_char",
            "__VERIFIER_nondet_short",
            "__VERIFIER_nondet_long",
            "__VERIFIER_error",
            "__VERIFIER_nondet_float",  
            "__VERIFIER_nondet_double"
        ]

    def visit_FuncDef(self, node):
        
        if node.decl.name in self.blacklisted_funcs:
            return ""
        return super().visit_FuncDef(node)

    def visit_Decl(self, node):
        if isinstance(node.type, c_ast.FuncDecl):
            if node.name in self.blacklisted_funcs:
                return ""
        return super().visit_Decl(node)

PROXY_HEADER = """
#include <stdio.h>
#include <stdlib.h>
#ifndef LARGE_INT
#define LARGE_INT 1000000
#endif

#ifndef MAX_INT
#define MAX_INT 2147483647
#endif

#ifndef INT_MAX
#define INT_MAX 2147483647
#endif

#ifndef INT_MIN
#define INT_MIN (-2147483647 - 1)
#endif

#ifndef UINT_MAX
#define UINT_MAX 4294967295U
#endif
"""

RANDOM_PROXY_HEADER = """
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#ifndef LARGE_INT
#define LARGE_INT 1000000
#endif

#ifndef MAX_INT
#define MAX_INT 2147483647
#endif

#ifndef INT_MAX
#define INT_MAX 2147483647
#endif

#ifndef INT_MIN
#define INT_MIN (-2147483647 - 1)
#endif

#ifndef UINT_MAX
#define UINT_MAX 4294967295U
#endif
//  nondet_char
char __VERIFIER_nondet_char() {
    static int seeded = 0;
    if (!seeded) { srand(time(NULL)); seeded = 1; }
    return (char)(rand() % 256); 
}
//  nondet_short
short __VERIFIER_nondet_short() {
    static int seeded = 0;
    if (!seeded) { srand(time(NULL)); seeded = 1; }
    return (short)(rand() % 100); 
}

//  nondet_long
long __VERIFIER_nondet_long() {
    static int seeded = 0;
    if (!seeded) { srand(time(NULL)); seeded = 1; }
    return ((long)rand() << 32) | (long)rand(); 
}
//  nondet_bool
_Bool __VERIFIER_nondet_bool() {
    static int seeded = 0;
    if (!seeded) { srand(time(NULL)); seeded = 1; }
    return (_Bool)(rand() % 2);
}
//  nondet_float 
float __VERIFIER_nondet_float() {
    static int seeded = 0;
    if (!seeded) { srand(time(NULL)); seeded = 1; }
    return ((float)rand() / (float)(RAND_MAX)) * 200.0f - 100.0f; 
}

//  nondet_double
double __VERIFIER_nondet_double() {
    static int seeded = 0;
    if (!seeded) { srand(time(NULL)); seeded = 1; }
    return ((double)rand() / (double)(RAND_MAX)) * 200.0 - 100.0;
}
//  nondet_int
int __VERIFIER_nondet_int() {
    static int seeded = 0;
    if (!seeded) { 
        srand(time(NULL)); 
        seeded = 1; 
    }
    return (rand() % 201) - 100; 
}

//  nondet_uint
unsigned int __VERIFIER_nondet_uint() {
    static int seeded = 0;
    if (!seeded) { 
        srand(time(NULL)); 
        seeded = 1; 
    }
    return (unsigned int)(rand() % 1000); 
}

void reach_error() { 
    printf("REACH_ERROR called!\\n"); 
    exit(1); 
}

void __VERIFIER_assert(int cond) {
    if (!(cond)) {
        printf("Assertion failed!\\n");
        exit(1);
    }
}

void assume_abort_if_not(int cond) {
    if (!cond) exit(0);
}
"""
def get_final_Ccode(ast, boogie_model_text):
    
    model_data = parse_boogie_model(boogie_model_text)
    generator = InstrumentingGenerator(model_data)
    final_c_code = generator.visit(ast)
    
    final_c_code = PROXY_HEADER + final_c_code
    return final_c_code
def get_final_Ccode_2(ast):
    generator = RandomInputGenerator()
    
    c_code_body = generator.visit(ast)
    
    final_code = RANDOM_PROXY_HEADER + "\n" + c_code_body
    
    return final_code 

if __name__ == "__main__":
    boogie_log = """
*** MODEL
result -> 
snap_nondet_0 -> 
snap_nondet_0@0 -> (- 4)
snap_nondet_1 -> 
snap_nondet_1@0 -> 0
v -> 
v@0 -> 4
v@1 -> (- 108)
v@2 -> 0
v@3 -> 0
v@4 -> 0
x -> 
X -> 
x@0 -> (- 1)
X@0 -> (- 4)
x@1 -> 0
xy -> 
xy@1 -> 56
xy@2 -> 14
y -> 
Y -> 
y@0 -> (- 14)
Y@0 -> 0
y@1 -> 0
y@2 -> 0
yx -> 
yx@1 -> 0
yx@2 -> 0
ControlFlow -> {
  0 0 -> 15
  0 10 -> 9
  0 12 -> 10
  0 13 -> 12
  0 15 -> 13
  0 5 -> 27
  0 7 -> (- 6)
  0 9 -> 7
  else -> 9
}
tickleBool -> {
  false -> true
  true -> true
  else -> true
}
*** STATE <initial>
  result -> 
  snap_nondet_0 -> 
  snap_nondet_1 -> 
  v -> 
  x -> 
  X -> 
  xy -> 
  y -> 
  Y -> 
  yx -> 
*** END_STATE
*** END_MODEL
    """
    parsed = parse_boogie_model(boogie_log)
    print(json.dumps(parsed, indent=2))