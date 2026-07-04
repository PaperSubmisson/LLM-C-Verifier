import os
import re
import subprocess
import copy
import json
import logging
import concurrent.futures
from openai import OpenAI
from pycparser import c_parser, c_ast
from translator_v2 import trans_c_to_boogie, preprocess_code,insert_inv_to_boogie_with_snap,insert_inv_to_boogie_FULLSNAP
from c_instrumenter import get_final_Ccode, parse_boogie_model, get_final_Ccode_2

# ================= Config section =================
API_KEY = "" 
BASE_URL = "" 
MODEL_NAME = "" 
TARGET_FOLDER = "benchmark/task?"   #select the task folder(task1-task6)
MAX_WORKERS = 150                    # Number of concurrent tasks
LOG_FOLDER = f"{TARGET_FOLDER}/logs"         
# ===========================================
COMMON_PROMPT = """
[Boogie Core Syntax Guide]
Please strictly use only the following Boogie-native syntax. Do NOT use symbols specific to other programming languages (such as %, <<, >>) or non-standard aggregate notation (such as sum, product):

1. Types and Arithmetic Operations (Extremely Important; Boogie is strictly strongly typed):
   - Integers (`int`): use `+`, `-`, and `*` for addition, subtraction, and multiplication. Integer division must use `div` (e.g., `x div 2`), and modulo must use `mod` (e.g., `x mod 2`).
   - Reals (`real`): correspond to C `float`/`double`. Use `+`, `-`, and `*` for addition, subtraction, and multiplication. Real division must use `/` (e.g., `x / 2.0`).
   - Fatal warning about type mixing: Boogie absolutely forbids mixed arithmetic or comparison between `int` and `real`. For example, `real_var - int_var` will cause a syntax error.
     - Correct approach: when writing contracts, both sides of an equality must have pure types. If you must use an integer variable in a real-valued formula, use the built-in conversion function `real(int_var)` to cast it to `real` before performing operations.
       Wrong example: `(4.0 * s) - (12 * r) == 1.0`  (assuming `r` is an `int`)
       Correct example: `(4.0 * s) - (12.0 * real(r)) == 1.0`

2. Logical Operations:
   - Basic operators: `&&` (and), `||` (or), `!` (not), `==` (equals), `!=` (not equals).
   - Implication: `==>` (e.g., `x > 0 ==> y > 0`).
   - Biconditional: `<==>`.
   - Strict parentheses requirement: Boogie absolutely forbids mixing `&&` and `||` without explicit parentheses! For example, writing `A && B || C && D` will directly trigger a syntax error. You must parenthesize them explicitly: write `(A && B) || (C && D)`.
   - Parenthesizing implications: to avoid precedence confusion, when using `==>`, you must fully parenthesize both the antecedent and the consequent. For example: `(A && B) ==> (C || D)`.

3. Quantifiers:
   - Universal: `forall k: int :: 0 <= k && k < n ==> a[k] == 0`
   - Existential: `exists k: int :: a[k] == target`

4. Conditional Expressions:
   - Use `if ... then ... else ...` (for example, `val == (if x > 0 then x else -x)`), and do not use the `?:` ternary operator.

[Global Flat Memory Model and Contract-Writing Guidelines]
The current Boogie program uses a global flat memory model. Complex data structures are uniformly stored in the following global maps:

Memory components:
- `Mem_int: [int]int`
  Global integer memory.
- `Mem_real: [int]real`
  Global real-valued memory.
- `Alloc: [int]bool`
  Allocation-validity map. If `Alloc[base] == true`, then the base address is live/valid.
- `Size: [int]int`
  Records the total number of contiguous memory cells allocated at a base address. It is used for bounds checking.

Address variables and offsets:
- In the Boogie code, some variables may appear to be ordinary `int` variables, such as `in_p` or `in_a`. However, if such a variable is used as an index into `Mem_int` or `Mem_real`, for example in an expression like `Mem_int[in_a + i]`, then it should be understood as a memory base address.
- Data reads and writes are represented as map accesses with offsets.

Mandatory rules for writing memory-related contracts:
1. Validity and aliasing
- If a parameter is used as a memory address, such as `in_p`, its validity must be declared in the `requires` clause:
  `requires in_p > 0 && Alloc[in_p] == true;`
- If there are multiple pointer-like parameters and their memory regions should not overlap, you must add a separation condition in the `requires` clause:
  `requires (in_a + Size[in_a] <= in_b) || (in_b + Size[in_b] <= in_a);`

2. Bounds safety
- If the code accesses `Mem_...[in_p + i]`, the contract must ensure that the access is in bounds:
  `0 <= i && i < Size[in_p];`

3. Frame problem and loop amnesia for global memory  [Extremely important]
- Pay close attention to the `modifies` clause in each procedure signature. Whenever a global variable such as `Mem_int`, `Mem_real`, `Alloc`, `Size`, or `Allocator` appears in the `modifies` list, the solver requires an explicit description of its state when the procedure exits.
- Protecting data memory (`Mem_xxx`):
  If `Mem_xxx` is modified by the procedure, you must explicitly state in the `ensures` clause that all memory regions not actually modified by the procedure remain unchanged when the procedure exits.
  Generic example:
  `ensures (forall addr: int :: !(addr is in the modified range) ==> Mem_int[addr] == old(Mem_int)[addr]);`
- Protecting allocation state (`Alloc`, `Size`):
  If `Alloc` and `Size` are modified, and the procedure only allocates new memory without freeing old memory, then you must guarantee in the `ensures` clause that all previously allocated memory remains valid and keeps the same size after the procedure exits.
  Example:
  `ensures (forall addr: int :: old(Alloc)[addr] == true ==> Alloc[addr] == true && Size[addr] == old(Size)[addr]);`
- Protecting the allocation cursor (`Allocator`):
  If `Allocator` is modified, you must ensure that the allocator is monotonically nondecreasing at procedure exit, so that it does not move backwards and overwrite old data.
  Example:
  `ensures Allocator >= old(Allocator);`
- For `loop_X` procedures:
  You must add corresponding anti-amnesia assertions as loop `invariant`s as well, such as preservation of old allocation validity and preservation of unmodified memory regions. Otherwise, the verifier will not be able to prove the `ensures` clauses.

4. Preventing context loss through strict preconditions
- Modular verification means that each procedure is verified in isolation. The solver may assign adversarial arbitrary values to all `in_` parameters.
- Therefore, you must constrain all input parameters precisely in the `requires` clauses, especially variables used as state flags or loop counters. For example, if a flag is initialized to `1` before entering a loop, you must explicitly write `requires in_flag == 1;`. Otherwise, the solver may instantiate it as `0`, which can break subsequent reasoning.

5. Quantifiers and relational arrays  [Extremely important]
- SMT solvers such as Z3 are very sensitive to quantifiers. In particular, Z3 often performs poorly when map indices contain arithmetic expressions such as `Mem_int[in_a + k]`. Such expressions may lead to ineffective triggers and spurious counterexamples.
- rule:
  In any `forall` formula that traverses an array, the quantified variable must represent an absolute address, such as `addr`, and the map access should be written directly as `Mem_int[addr]`.
- Bad style, which often makes Z3 fail:
  `forall k: int :: 0 <= k && k < n ==> Mem_int[in_acopy + k] == Mem_int[in_a + k]`
- Correct style:
  `forall addr: int :: in_acopy <= addr && addr < in_acopy + n ==> Mem_int[addr] == Mem_int[in_a + (addr - in_acopy)]`
- For assignment-copy loops, comparison-check loops, or any loop that traverses an array, always use the absolute-address style above. Do not use a relative offset variable such as `k` as the direct quantified index.

6. Loop counter monotonicity
- When Boogie verifies loop preservation, it havoc-randomizes all modified variables.
- If a loop variable such as `i` increases from an initial value, you must explicitly state its relation to the initial parameter in the loop invariant.
  Example:
  `invariant i >= in_i;`

7. Strict restrictions on the `old()` keyword
- The expression `old(e)` means the value of expression `e` in the initial state at procedure entry.
- Never use `old()` in a `requires` clause. At procedure entry, the current state is already the initial state, so you should directly write expressions such as `Mem_int[addr]`. Using `old()` in a `requires` clause will cause a syntax error.
- `old()` may only be used in `ensures` clauses and loop `invariant`s, where it refers to the old memory state at procedure entry.
  Correct example:
  `Mem_int[addr] == old(Mem_int)[addr]`

[Advanced Guidance: Auxiliary Functions and Axioms]
Use the "global" field to introduce auxiliary functions and axioms only when the required program logic cannot be expressed directly using ordinary `requires`, `ensures`, and `invariant` clauses. 
Typical examples include nonlinear arithmetic, recursive summaries, and array aggregations such as sums or maxima.

Critical Rule: Boogie Functions Are Pure
Boogie `function` declarations and `axiom` declarations are pure mathematical definitions. 
They are not allowed to refer directly to global program variables such as `Mem_int`, `Mem_real`, `Alloc`, or `Size`. 
If they do, Boogie will report an error such as "cannot refer to a global variable".
Therefore, whenever an auxiliary function needs to inspect memory, the relevant memory map must be passed explicitly as an argument. 
For example, use a parameter of type `[int]int` or `[int]real`, and quantify over this parameter in the axioms: `forall M: [int]int :: ...`

[Scenario A: Nonlinear Numeric Evolution, e.g., Multiplication, Division, Exponentiation, or Shifts]
If a variable follows a regular nonlinear evolution pattern, such as `v = v * 2`, define a mapping function rather than a Boolean predicate.

- Definition example:
  `function Pow2(k: int) : int;`
  If the values are real-valued, use `real` instead of `int`.
- Axioms:
  The axioms should include a base case, a recurrence rule, and, when necessary, an inverse or monotonicity-related rule.
- Usage example:
  `(exists k: int :: v == Initial_Val * Pow2(k))`

[Scenario B: Array Aggregation, e.g., Sum, Maximum, and the Direction-Consistency Rule]
If the proof involves a recursive aggregation over an array range, such as `Sum` or `MaxVal`, the unfolding direction of the recursive axiom must be consistent with the direction in which the loop progresses.

If the loop variable `i` increases from left to right, i.e., the loop extends the processed interval to the right, then the recursive axiom should peel off the right endpoint.

Correct example: right-endpoint unfolding for summation.

`function Sum(M: [int]int, base: int, start: int, end: int) : int;`

`axiom (forall M: [int]int, base: int, start: int, end: int :: start >= end ==> Sum(M, base, start, end) == 0);`

`axiom (forall M: [int]int, base: int, start: int, end: int :: start < end ==> Sum(M, base, start, end) == Sum(M, base, start, end - 1) + M[base + end - 1]);`

This form matches naturally with an `i++` loop, because Z3 can instantiate the recurrence when the loop grows the range by one element on the right.

[Output Format Requirements]
Please return only a valid JSON object, without Markdown formatting or other explanations.
The JSON structure is shown in the example below; omit the "global" item when no auxiliary functions or axioms are needed：
{{
  "global": [
    "function Pow2(k: int) : int;",
    "axiom Pow2(0) == 1;",
    "axiom (forall k: int :: k > 0 ==> Pow2(k) == 2 * Pow2(k-1));",
    "axiom (forall k: int :: k >= 0 ==> 2 * Pow2(k) == Pow2(k+1));",
    "axiom (forall k: int :: k >= 0 ==> Pow2(k) > 0);"
  ],
  "procedure name (e.g., loop_0)": {{
    "requires": ["condition expression 1", "condition expression 2"],
    "ensures": ["condition expression 1", "condition expression 2"],
    "invariants(can be omitted if there are no loops inside the procedure)": ["condition expression 1", "condition expression 2"]
  }},
  ...
}}

[Notes]
1. Please use only core Boogie syntax in expressions. Using undefined functions or chained comparisons such as `a <= b <= c` will cause syntax errors.
2. Requires (preconditions): a `requires` clause may refer only to input parameters whose names start with `in_` (e.g., `in_x`) and global variables. It is strictly forbidden to refer to local variables or return variables without the `in_` prefix, such as `x` or `i`.
3. Ensures (postconditions): an `ensures` clause may refer only to input parameters whose names start with `in_`, return variables declared in the `returns` clause, and global variables.
4. for a procedure declared as `procedure sum(...) returns (...)`, the procedure name is `sum`.
5. Boogie verifies loops inductively. The verification logic is:
   - Loop entry: `Loop_Head_State` must satisfy `(Invariant) && (Loop_Condition)`.
   - Loop exit: `Exit_State` must satisfy `(Invariant) && !(Loop_Condition)`.
"""

def setup_task_logger(task_id):
    logger = logging.getLogger(task_id)
    logger.setLevel(logging.INFO)
    
    if logger.handlers:
        logger.handlers = []

    log_path = os.path.join(LOG_FOLDER, f"{task_id}.log")
    file_handler = logging.FileHandler(log_path, mode='w', encoding='utf-8')
    formatter = logging.Formatter('%(asctime)s - %(message)s')
    file_handler.setFormatter(formatter)
    
    logger.addHandler(file_handler)
    
    logger.propagate = False 
    
    return logger

try:
    global_openai_client = OpenAI(api_key=API_KEY, base_url=BASE_URL)
except Exception as e:
    print(f"Global OpenAI client initialization failed: {e}")
    exit(1)

class LLMClient:
    def __init__(self, name, role):
        self.name = name
        self.role = role

        self.client = global_openai_client

    def query(self, prompt, logger):
        if not hasattr(self, 'client') or self.client is None:
            logger.error("API client not initialized, cannot make a request.")
            return None
        logger.info(f">>> Sending request to {self.name} ...")
        
        messages = [
            {"role": "system", "content": self.role},
            {"role": "user", "content": prompt}
        ]
        
        try:
            response = self.client.chat.completions.create(
                model=MODEL_NAME,
                messages=messages,
                temperature=0.7, 
            )
            
            content = response.choices[0].message.content
            
            logger.info(f"<<< {self.name} : \n{content}\n{'='*20}")
            return content
        except Exception as e:
            logger.error(f"API call error: {e}")
            return None

class BoogieFeedbackGenerator:
    def __init__(self, bpl_code, model_data, var_types, snapshot_is_address, struct_env):
        self.bpl_lines = bpl_code.split('\n')
        self.model_data = parse_boogie_model(model_data)
        self.var_types = var_types
        self.snapshot_is_address = snapshot_is_address
        self.struct_env = struct_env

        self.proc_line = {}
        self.line_map = self._build_line_map()
        cleaned_lines = []
        for line in self.bpl_lines:
            
            if "//" in line:
                line = line.split("//")[0]
            
            cleaned_lines.append(line.rstrip())
            
        self.bpl_lines = cleaned_lines

    def _build_line_map(self):
        mapping = {}
        
        current_module = "global"  
        current_loop_id = 0        
        fallback_assertion_counter = 0 
        
        last_seen_assertion_snap_id = None 
        re_proc = re.compile(r'procedure\s+(\w+)')
        re_call = re.compile(r'call\s+(?:[\w\s,]+:=\s+)?(\w+)\(')
        re_call_id_comment = re.compile(r'//\s*CallID:\s*(\d+)')
        re_snap_assign = re.compile(r'snap_assertion(\d+)_\w+\s*:=')
        for idx, line in enumerate(self.bpl_lines):
            line_num = idx + 1
            stripped = line.strip()
            
            if stripped.startswith("snap_assertion"):
                match = re_snap_assign.match(stripped)
                if match:
                    last_seen_assertion_snap_id = match.group(1)
            
            proc_match = re_proc.match(stripped)
            if proc_match:
                current_module = proc_match.group(1)
                self.proc_line[current_module] = line_num
                
                if current_module.startswith("loop_"):
                    try:
                        current_loop_id = int(current_module.split('_')[1])
                    except (IndexError, ValueError):
                        current_loop_id = 0
                else:
                    current_loop_id = 0
            
            stmt_type = "common"
            stmt_info = "0"
            
            if stripped.startswith("assert"):
                stmt_type = "assert"
                
                if "[Safety]" in stripped:
                    stmt_info = f"safety_{fallback_assertion_counter}"
                    fallback_assertion_counter += 1
                else:
                    if last_seen_assertion_snap_id is not None:
                        
                        stmt_info = last_seen_assertion_snap_id
                        
                        last_seen_assertion_snap_id = None
                    else:
                        stmt_info = f"{fallback_assertion_counter}"
                        fallback_assertion_counter += 1
                
            
            elif stripped.startswith("call"):
                stmt_type = "call"
                call_match = re_call.match(stripped)
                if call_match:
                    stmt_info = call_match.group(1) 
                    id_match = re_call_id_comment.search(stripped)
                    if id_match:
                        stmt_info = id_match.group(1)
                else:
                    stmt_info = "unknown_call"
            
            mapping[line_num] = {
                "module": current_module,   
                "loop_id": current_loop_id, 
                "type": stmt_type,          
                "info": stmt_info,          
                "msg": stripped             
            }    
        return mapping

    def _parse_map_string(self, map_str):
        res = {}
        if not map_str or map_str == "Unknown Array":
            return res
            
        for item in map_str.split(','):
            item = item.strip()
            if "=" in item and "[" in item:
                
                m = re.search(r'\[(-?\d+)\]=(.*)', item)
                if m:
                    res[int(m.group(1))] = m.group(2).strip()
        return res

    def _detect_memory_overlap(self, snap_prefix):
        
        target_prefix = snap_prefix + "_" if not snap_prefix.endswith("_") else snap_prefix
        
        mem_blocks = {} 
        
        alloc_map = {}
        size_map = {}
        
        for key, val in self.model_data.items():
            clean_key = key.split('@')[0]
            if clean_key == f"{target_prefix}Alloc":
                alloc_map = self._parse_map_string(val)
            elif clean_key == f"{target_prefix}Size":
                size_map = self._parse_map_string(val)
                
        for key, val in self.model_data.items():
            clean_key = key.split('@')[0]
            if clean_key.startswith(target_prefix):
                var_name = clean_key[len(target_prefix):]
                
                if clean_key in self.snapshot_is_address:
                    try:
                        base_addr = int(val)
                        if alloc_map.get(base_addr, "false") == "true":
                            size = int(size_map.get(base_addr, 1))
                            mem_blocks[var_name] = (base_addr, size)
                    except:
                        pass
        
        warnings =[]
        vars_list = list(mem_blocks.keys())
        for i in range(len(vars_list)):
            for j in range(i + 1, len(vars_list)):
                v1, v2 = vars_list[i], vars_list[j]
                b1, s1 = mem_blocks[v1]
                b2, s2 = mem_blocks[v2]
                
                if not (b1 + s1 <= b2 or b2 + s2 <= b1):
                    warnings.append(f"    [{v1}] (base:{b1}, region:[{b1}, {b1+s1})) and [{v2}] (base:{b2}, region:[{b2}, {b2+s2})) are overlapping！")
                    
        return warnings

    def _get_vars_from_snapshot(self, prefix):
        target_prefix = prefix + "_" if not prefix.endswith("_") else prefix
        raw_vals = {}
        
        for key, val in self.model_data.items():
            if "@" in key:
                clean_key = key.split('@')[0] 
                if clean_key.startswith(target_prefix):
                    var_name = clean_key[len(target_prefix):] 
                    raw_vals[var_name] = val
        
        if not raw_vals:
            return "(No data)"

        mem_int = self._parse_map_string(raw_vals.get("Mem_int", ""))
        mem_real = self._parse_map_string(raw_vals.get("Mem_real", ""))
        alloc_map = self._parse_map_string(raw_vals.get("Alloc", ""))
        size_map = self._parse_map_string(raw_vals.get("Size", ""))

        result =[]
        
        for var_name, val in raw_vals.items():
            if var_name in["Mem_int", "Mem_real", "Alloc", "Size", "Allocator"]:
                continue
                
            full_snap_name = f"{target_prefix}{var_name}"
            is_address = full_snap_name in self.snapshot_is_address
            
            if not is_address:
                result.append(f"{var_name} = {val}")
                continue
                
            try:
                base_addr = int(val)
            except:
                result.append(f"{var_name} = {val} (Invalid Address Format)")
                continue
                
            is_alloc = alloc_map.get(base_addr, "false") == "true"
            
            if not is_alloc:
                result.append(f"{var_name} = {base_addr} (INVALID / NULL / Freed)")
                continue
                
            alloc_size = int(size_map.get(base_addr, 1))
            mem_slice =[]
            
            for target_addr, m_val in mem_int.items():
                if base_addr <= target_addr < base_addr + alloc_size:
                    offset = target_addr - base_addr
                    addr_expr = var_name if offset == 0 else f"{var_name} + {offset}"
                    mem_slice.append(f"Mem_int[{addr_expr}] = {m_val}")
                    
            for target_addr, m_val in mem_real.items():
                if base_addr <= target_addr < base_addr + alloc_size:
                    offset = target_addr - base_addr
                    addr_expr = var_name if offset == 0 else f"{var_name} + {offset}"
                    mem_slice.append(f"Mem_real[{addr_expr}] = {m_val}")
                    
            slice_str = ""
            if mem_slice:
                slice_str = "\n    " + "\n    ".join(mem_slice)
            else:
                slice_str = "  (The value of this memory block is left to Z3's discretion or kept in a Havoc state, which typically does not affect the core logic of the counterexample.)"
                
            result.append(f"{var_name} = {base_addr} (valid memory, Size: {alloc_size}){slice_str}")

        result.sort()
        return "\n  ".join(result)

    def _find_next_procedure_start(self, error_line):
        
        total_lines = len(self.bpl_lines)
        
        for idx in range(error_line, total_lines):
            line = self.bpl_lines[idx].strip()
            
            if line.startswith("procedure"):
                return idx + 1 
        
        return None 

    def generate_report(self, boogie_output):
        match = re.search(r'\.bpl\((\d+),\d+\): Error: (.*)', boogie_output)

        if not match:
            return "No standard Boogie error format detected."
            
        error_line = int(match.group(1))
        error_msg = match.group(2).strip()
        end_line = self._find_next_procedure_start(error_line)
        
        err_info = self.line_map.get(error_line)
        if not err_info: return f"Unable to locate context for line number {error_line}."
        
        module = err_info['module']
        loop_id = err_info['loop_id']
        type = err_info['type']
        info = err_info['info']
        msg = err_info['msg']
        
        is_loop = module.startswith("loop_")

        start_line = self.proc_line.get(module)
        if not start_line: return f"Unable to locate position in module {module}."

        report = f"[Verification Failure Report]\n"
        report += f"Location: procedure {module}\n"
        report += f"Error message: for procedure {module}，boogie returned {error_msg}\n"
        
        if "this assertion could not be proved" in error_msg:
            state = self._get_vars_from_snapshot(f"snap_assertion{info}")
            report += "Execution trace:\n"
            if is_loop:
                state_entry = self._get_vars_from_snapshot(f"snap_loop{loop_id}_entry")
                report += f"-> At the external entry point of the loop, the variable state provided by Boogie according to the requires(precondition) is：\n{state_entry}\n"
            else:
                state_entry = self._get_vars_from_snapshot(f"snap_{module}_entry")
                report += f"-> At the entry of {module}, the variable state provided by Boogie according to the requires(precondition) is：\n{state_entry}\n"
            after_while = False
            after_call = False
            for i in range(start_line, error_line):
                trace_info = self.line_map.get(i)
                if is_loop and trace_info and 'while' in trace_info['msg']:
                    after_while = True
                    s1 = self._get_vars_from_snapshot(f"snap_loop{loop_id}_head")
                    report += f"-> At the beginning of the loop body, the variable state provided by Boogie according to the verification logic is：\n{s1}\n"
                elif trace_info and 'call ' in trace_info['msg']:
                    after_call = True
                    callee = trace_info['info']
                    if "loop" in callee:
                        s2 = self._get_vars_from_snapshot(f"snap_{callee}_called")
                    else:
                        s2 = self._get_vars_from_snapshot(f"snap_call_{callee}_post")
                    report += f"-> After {trace_info['msg']}, the variable state provided by Boogie according to the ensures (postcondition) of the called procedure is：\n{s2}\n"
            report += f"-> {msg} does not hold; the variable state at this point is：\n{state}\n"
            
            if "[Safety] Null pointer deref" in msg:
                report += f"-> (Hint) Null Pointer Dereference occurred! Please check whether the pointer is properly allocated, or add a constraint such as ptr > 0 in the Requires/Invariant clauses.\n"
            elif "[Safety] Free Non-null" in msg:
                report += f"-> (Hint) Attempt to free a null pointer! Please check whether the pointer is properly allocated, or add a constraint such as ptr > 0 in the Requires/Invariant clauses.\n"
            elif "[Safety] Use-After-Free" in msg:
                report += f"-> (Hint) Memory safety error: attempted to access invalid memory (Use‑After‑Free)! Please check whether the validity constraint Alloc[ptr] == true is included in the Requires/Invariant clauses.\n"
            elif "[Safety] Prevent Double Free" in msg:
                report += f"-> (Hint) Memory safety error: attempted to free invalid memory (Double Free)! Please check whether the validity constraint Alloc[ptr] == true is included in the Requires/Invariant clauses.\n"
            else:
                if after_while:
                    report += f"-> (Hint) Please check whether the loop invariant inside {module} needs to be strengthened or corrected.\n"
                if after_call:
                    report += f"-> (Hint) Please check whether the ensures (postcondition) of the called procedure needs to be strengthened or corrected.\n"
                report += f"-> (Hint) Please check whether the requires (precondition) of {module} needs to be strengthened or corrected.\n"

        elif "this loop invariant could not be proved on entry" in error_msg:
            state = self._get_vars_from_snapshot(f"snap_loop{loop_id}_entry")
            report += "Execution trace:\n"
            for i in range(start_line, error_line):
                trace_info = self.line_map.get(i)
                if trace_info and 'while' in trace_info['msg']:
                    s1 = self._get_vars_from_snapshot(f"snap_loop{loop_id}_entry")
                    report += f"-> At the external entry point of the loop, the variable state provided by Boogie according to the requires(precondition) is：\n{s1}\n"
            report += f"-> {msg} does not hold; the variable state at this point is：\n{state}\n"
            report += f"-> (Hint) Please check whether the requires (precondition) of {module} needs to be strengthened or corrected.\n"
            report += f"-> (Hint) Please check whether the invariant itself needs to be corrected.\n"

        elif "this invariant could not be proved to be maintained by the loop" in error_msg:
            state = self._get_vars_from_snapshot(f"snap_loop{loop_id}_body")
            report += "Execution trace:\n"
            if "loop" in module:
                state_entry = self._get_vars_from_snapshot(f"snap_loop{loop_id}_entry")
                report += f"-> At the external entry point of the loop, the variable state provided by Boogie according to the requires(precondition) is：\n{state_entry}\n"
            after_call = False
            for i in range(start_line, end_line):
                trace_info = self.line_map.get(i)
                if trace_info and 'while' in trace_info['msg']:
                    s1 = self._get_vars_from_snapshot(f"snap_loop{loop_id}_head")
                    report += f"-> At the beginning of the loop body, the variable state provided by Boogie according to the verification logic is：\n{s1}\n"
                elif trace_info and 'call ' in trace_info['msg']:
                    after_call = True
                    callee = trace_info['info']
                    if "loop" in callee:
                        s2 = self._get_vars_from_snapshot(f"snap_{callee}_called")
                    else:
                        s2 = self._get_vars_from_snapshot(f"snap_call_{callee}_post")
                    report += f"-> After {trace_info['msg']}, the variable state provided by Boogie according to the ensures (postcondition) of the called procedure is：\n{s2}\n"
            report += f"-> At the end of the loop body, {msg} does not hold; the variable state at this point is：\n{state}\n"
            report += f"-> (Hint) Please check whether the loop invariant inside {module} needs to be strengthened or corrected.\n"
            report += f"-> (Hint) If auxiliary functions and axioms are involved, consider checking whether they need to be supplemented or revised.\n"
            if after_call:
                report += f"-> (Hint) Please check whether the ensures (postcondition) of the called procedure needs to be strengthened or corrected.\n"

        elif "a precondition for this call could not be proved" in error_msg:
            if "loop" in info:
                state = self._get_vars_from_snapshot(f"snap_{info}_call")
            else:
                state = self._get_vars_from_snapshot(f"snap_call_{info}_pre")
            report += "Execution trace:\n"
            if is_loop:
                state_entry = self._get_vars_from_snapshot(f"snap_loop{loop_id}_entry")
                report += f"-> At the external entry point of the loop, the variable state provided by Boogie according to the requires(precondition) is：\n{state_entry}\n"
            else:
                state_entry = self._get_vars_from_snapshot(f"snap_{module}_entry")
                report += f"-> At the entry of {module}, the variable state provided by Boogie according to the requires(precondition) is：\n{state_entry}\n"
            after_while = False
            after_call = False
            for i in range(start_line, error_line):
                trace_info = self.line_map.get(i)
                if trace_info and 'while' in trace_info['msg']:
                    after_while = True
                    s1 = self._get_vars_from_snapshot(f"snap_loop{loop_id}_head")
                    report += f"-> At the beginning of the loop body, the variable state provided by Boogie according to the verification logic is：\n{s1}\n"
                elif trace_info and 'call ' in trace_info['msg']:
                    after_call = True
                    callee = trace_info['info']
                    if "loop" in callee:
                        s2 = self._get_vars_from_snapshot(f"snap_{callee}_called")
                    else:
                        s2 = self._get_vars_from_snapshot(f"snap_call_{callee}_post")
                    report += f"-> After {trace_info['msg']}, the variable state provided by Boogie according to the ensures (postcondition) of the called procedure is：\n{s2}\n"
            report += f"-> The requires(precondition) of {info} does not hold; the variable state at this point is：\n{state}\n"
            if after_while:
                report += f"-> (Hint) Please check whether the loop invariant inside {module} needs to be strengthened or corrected.\n"
            if after_call:
                report += f"-> (Hint) Please check whether the ensures (postcondition) of the called procedure needs to be strengthened or corrected.\n"
            report += f"-> (Hint) Please check whether the requires (precondition) of {module} needs to be strengthened or corrected.\n"
            report += f"-> (Hint) Please check whether the requires (precondition) of {msg} itself needs to be corrected.\n"

        elif "a postcondition could not be proved on this return path" in error_msg:
            report += "Execution trace:\n"
            if is_loop:
                state = self._get_vars_from_snapshot(f"snap_loop{loop_id}_done")
                state_entry = self._get_vars_from_snapshot(f"snap_loop{loop_id}_entry")
                report += f"-> At the external entry point of the loop, the variable state provided by Boogie according to the requires(precondition) is：\n{state_entry}\n"
                report += f"-> At the exit of the loop, the variable state provided by Boogie according to the verification logic is：\n{state}\n"
            else:
                state = self._get_vars_from_snapshot(f"snap_{module}_exit")
                state_entry = self._get_vars_from_snapshot(f"snap_{module}_entry")
                report += f"-> At the entry of {module}, the variable state provided by Boogie according to the requires (precondition) is：\n{state_entry}\n"
                for i in range(start_line, error_line):
                    trace_info = self.line_map.get(i)
                    if trace_info and 'call ' in trace_info['msg']:
                        after_call = True
                        callee = trace_info['info']
                        if "loop" in callee:
                            s2 = self._get_vars_from_snapshot(f"snap_{callee}_called")
                        else:
                            s2 = self._get_vars_from_snapshot(f"snap_call_{callee}_post")
                        report += f"-> After {trace_info['msg']}, the variable state provided by Boogie according to the ensures (postcondition) of the called procedure is：\n{s2}\n"
                report += f"-> At the exit of {module}, the variable state at this point is:\n{state}\n"
            post = ""
            for i in range(start_line, error_line):
                trace_info = self.line_map.get(i)
                if trace_info and 'ensures' in trace_info['msg']:
                    post = trace_info['msg']
                    break
            
            report += f"-> {post} does not hold; the variable state at this point is：\n{state}\n"
            report += f"-> (Hint) Please check whether the requires (precondition) of {module} itself needs to be strengthened or corrected.\n"
            if is_loop:
                report += f"-> (Hint) Please check whether the loop invariant inside {module} needs to be strengthened or corrected.\n"
            report += f"-> (Hint) Please check whether the ensures (postcondition) of {module} itself needs to be corrected.\n"
        else:
            report += "Unknown logic error; please inspect manually."
        
        snap_prefix_for_overlap = None
        if "this assertion could not be proved" in error_msg:
            snap_prefix_for_overlap = f"snap_assertion{info}"
            
        elif "this loop invariant could not be proved on entry" in error_msg:
            snap_prefix_for_overlap = f"snap_loop{loop_id}_entry"
            
        elif "this invariant could not be proved to be maintained by the loop" in error_msg:
            snap_prefix_for_overlap = f"snap_loop{loop_id}_body"
            
        elif "a precondition for this call could not be proved" in error_msg:
            if "loop" in str(info):
                snap_prefix_for_overlap = f"snap_{info}_call"
            else:
                snap_prefix_for_overlap = f"snap_call_{info}_pre"
                
        elif "a postcondition could not be proved on this return path" in error_msg:
            if is_loop:
                snap_prefix_for_overlap = f"snap_loop{loop_id}_done"
            else:
                snap_prefix_for_overlap = f"snap_{module}_exit"
        
            
        if snap_prefix_for_overlap:
            overlap_warnings = self._detect_memory_overlap(snap_prefix_for_overlap)
            if overlap_warnings:
                report += "\n[Memory Overlap Warning]\n"
                report += "In the counterexample constructed by Z3, the following memory blocks are found to overlap in physical addresses:\n"
                for w in overlap_warnings:
                    report += w + "\n"
                report += "-> (Hint) If this is not the intended aliasing behavior, be sure to add a separation assertion in the initial Requires or elsewhere, for example `(in_a + Size[in_a] <= in_b) || (in_b + Size[in_b] <= in_a)` to ensure memory safety.\n"
        return report

def extract_procedure_names(boogie_code):
    return re.findall(r'procedure\s+(\w+)\s*\(', boogie_code)

def run_boogie_tool(boogie_code, task_id, logger, seed=1):
    
    filename = f"task_{task_id}_{seed}.bpl" 
    model_filename = f"task_{task_id}_{seed}.model"
    try:
        with open(filename, "w") as f:
            f.write(boogie_code)
        
        proc_names = extract_procedure_names(boogie_code)
        
        for proc_name in proc_names:
            cmd = ["boogie",f"/proverOpt:O:smt.random_seed={seed}",  f"-proc:{proc_name}",f"-mv:{model_filename}","/timeLimit:15", filename]
        
            try:
                
                if os.path.exists(model_filename):
                    os.remove(model_filename)
                
                result = subprocess.run(cmd, capture_output=True, text=True, timeout= 17)
                output = result.stdout

                if "time out" in output.lower() or "timeout" in output.lower():
                    return False, {"type": "timeout", "data": "Z3 Solver Timeout"}
                
                if "0 errors" in output:
                    continue
                else:
                    if os.path.exists(model_filename):
                        with open(model_filename, "r") as mf:
                            model_content = mf.read()
                        return False, {"type": "logic", "data": model_content, "output": output}
                    else:
                        return False, {"type": "syntax", "data": output}
            except subprocess.TimeoutExpired:
                logger.warning(f"Boogie timeout")
                return False, {"type": "timeout", "data": "Subprocess TimeoutExpired"}
            except Exception as e:
                logger.error(f"Boogie error: {e}")
                return False, {"type": "error", "data": str(e)}
        
        return True, {}
    finally:
        if os.path.exists(filename): os.remove(filename)
        if os.path.exists(model_filename): os.remove(model_filename)
    
def run_smoke_test(boogie_code, task_id, logger, seed=1):
    filename = f"task_{task_id}_smoke_{seed}.bpl"
    try:
        with open(filename, "w") as f:
            f.write(boogie_code)
        proc_names = extract_procedure_names(boogie_code)
        
        for proc_name in proc_names:
            cmd = ["boogie", f"/proverOpt:O:smt.random_seed={seed}", f"-proc:{proc_name}", "/timeLimit:15", filename]
            try:
                result = subprocess.run(cmd, capture_output=True, text=True, timeout=17)
                output = result.stdout
                
                if "0 errors" in output:
                    return True, proc_name 
            except subprocess.TimeoutExpired:
                pass
            except Exception as e:
                pass
        
        return False, ""
    finally:
        if os.path.exists(filename): os.remove(filename)

def run_c_dynamic_analysis(debug_c_code, task_id, logger):
    
    c_filename = f"debug_task_{task_id}.c"
    exe_filename = f"./debug_task_{task_id}.exe"
    
    with open(c_filename, "w") as f:
        f.write(debug_c_code)
        
    
    try:
        compile_proc = subprocess.run(["gcc", c_filename, "-o", exe_filename], check=True, capture_output=True, text=True)
        
        run_result = subprocess.run([exe_filename], capture_output=True, text=True, timeout=5)

        trace_log = run_result.stdout
        
        return trace_log

    except Exception as e:
        logger.info(f" Error during dynamic execution of C code: {e}\n{debug_c_code}")
        
        return f"Execution Failed: {e}"
    finally:
        os.remove(c_filename)
        if os.path.exists(exe_filename):
            os.remove(exe_filename)

def verify_single_file(file_path):
    file_name = os.path.basename(file_path)
    
    task_id = file_name
    
    logger = setup_task_logger(task_id)
    logger.info(f"Starting to process file: {file_path}")
    
    agent_B1 = LLMClient("B1", "Expert in formal verification and Boogie syntax")

    with open(file_path, "r") as c:
        c_code = c.read()
    
    c_code = preprocess_code(c_code)
    logger.info(f"\nThe C code to be verified is:\n{c_code}\n")
    
    parser = c_parser.CParser()
    ast = parser.parse(c_code)

    max_retries = 10 
    boogie_template, v_types, ptr_types, s_env = trans_c_to_boogie(ast, {}) 
    logger.info(f"\nThe corresponding Boogie code is:\n{boogie_template}\n")
    
    prompt = f"""
{boogie_template}
Please analyze the semantics of this code, and then generate verification contracts using a 'modular verification' approach. 
Please complete the requires, ensures, and internal loop invariants for each procedure module, so that verification can be performed. The true in the code is a placeholder default value.

{COMMON_PROMPT}
"""

    for i in range(max_retries):
        logger.info(f"\n------- CEGIS round {i+1}  -------")
        c_code_run0 = get_final_Ccode_2(ast)
        execution_trace = run_c_dynamic_analysis(c_code_run0,task_id,logger)
        if "Assertion failed" in execution_trace:
            logger.info("\nThe program itself contains errors; verification complete.")
            return f"{file_name}: BUG_FOUND"
        
        invariant = agent_B1.query(prompt, logger)
        
        if invariant is None:
            logger.warning("API request failed or timed out; waiting 3 seconds before retrying this round...")
            import time
            time.sleep(3)
            continue  
        try:
            
            clean_json = invariant.replace("```json", "").replace("```", "").strip()
            
            start_idx = clean_json.find('{')
            end_idx = clean_json.rfind('}')
            if start_idx != -1 and end_idx != -1:
                clean_json = clean_json[start_idx:end_idx+1]
            
            
            json.loads(clean_json) 
            invariant = clean_json
        except Exception as e:
            continue 

        boogie_final, _, _, _ = trans_c_to_boogie(ast, invariant)
        success, result = run_boogie_tool(boogie_final,task_id,logger) 
        
        if success:
            boogie_smoke, _, _, _ = trans_c_to_boogie(ast, invariant, smoke_test=True)
            
            dummy_logger = logging.getLogger("dummy_smoke_logger")
            dummy_logger.addHandler(logging.NullHandler())
            dummy_logger.propagate = False
            
            smoke_success, _ = run_smoke_test(boogie_smoke, task_id + "_smoke", dummy_logger)
            if smoke_success:
                continue 
            logger.info(f"\nSuccess! Verification complete. The full Boogie code is: \n{boogie_final}")
            return f"{file_name}: SUCCESS"
        
        failure_type = result.get("type", "error")
        failure_data = result.get("data", "")

        execution_trace = ""

        if failure_type == "timeout":
            logger.warning(f" Solver timeout: the quantifiers generated by the LLM are too complex; proceeding to the next round...")
            continue
        elif failure_type == "syntax":
            logger.error(f" Syntax error occurred. Please check the translator logic... The Boogie code is: \n{boogie_final}")
            
            continue
        elif failure_type == "logic":
            logger.info(f" Verification logic failed; entering dynamic analysis...")
            
            ast_copy = copy.deepcopy(ast)
            boogie_snap, _, _, _ = insert_inv_to_boogie_with_snap(ast_copy,invariant)
            state, msg = run_boogie_tool(boogie_snap,task_id,logger)
            if not state:
                model_data = msg.get("data","")
                ast_copy = copy.deepcopy(ast)
                c_code_run =  get_final_Ccode(ast_copy,model_data)
                execution_trace = run_c_dynamic_analysis(c_code_run,task_id,logger)
        
       
        if "Assertion failed" in execution_trace:
            logger.info("\nThe program itself contains errors; verification complete.")
            return f"{file_name}: BUG_FOUND"
        else:
            ast_copy = copy.deepcopy(ast)
            boogie_FULLSNAP, v_types, ptr_types, s_env  = insert_inv_to_boogie_FULLSNAP(ast_copy,invariant)
            
            state1, msg1 = run_boogie_tool(boogie_FULLSNAP,task_id,logger,seed=1)
            output1 = msg1.get("output","")
            model_data1 = msg1.get("data","")

            state2, msg2 = run_boogie_tool(boogie_FULLSNAP,task_id,logger,seed=2)
            output2 = msg2.get("output","")
            model_data2 = msg2.get("data","")
            
            feedback1 = BoogieFeedbackGenerator(boogie_FULLSNAP, model_data1, v_types, ptr_types, s_env)
            report1 = feedback1.generate_report(output1)
            
            feedback2 = BoogieFeedbackGenerator(boogie_FULLSNAP, model_data2, v_types, ptr_types, s_env)
            report2 = feedback2.generate_report(output2)
            
            
            prompt = f"{boogie_final}\n"
            prompt += "### Verification failed: two counterexample scenarios were found. ###\n"
            prompt += f"--- Counterexample scenario A ---\n{report1}\n"
            prompt += f"--- Counterexample scenario B ---\n{report2}\n"
            prompt += f"""
Based on the above information, please further refine the input state (Requires) and output state (Ensures) of the corresponding modules, as well as the internal invariants (Invariants), so that the reported errors are fixed.
The output must return the requires, ensures, and invariants for all procedure modules, and if there are auxiliary functions and axioms, they must be returned together under the global item.

{COMMON_PROMPT}
"""
            logger.info(prompt)

    logger.info(f"Maximum retry attempts reached; verification stopped.\n")
    return f"{file_name}: TIMEOUT"


if __name__ == "__main__":
    
    if not os.path.exists(TARGET_FOLDER):
        os.makedirs(TARGET_FOLDER)
        print(f"Please create the {TARGET_FOLDER} folder and place the code inside.")
        exit()
        
    if not os.path.exists(LOG_FOLDER):
        os.makedirs(LOG_FOLDER)

    files = [os.path.join(TARGET_FOLDER, f) for f in os.listdir(TARGET_FOLDER) if f.endswith(".c")]
    
    if not files:
        print("No files.")
        exit()

    print(f"Starting verification of {len(files)} tasks...")
    print(f"For detailed logs, please check the individual log files under the {LOG_FOLDER} folder.")

    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        future_to_file = {executor.submit(verify_single_file, f): f for f in files}
        
        for future in concurrent.futures.as_completed(future_to_file):
            file_name = future_to_file[future]
            try:
                res = future.result()
                results.append(res)
                
                print(f"[{file_name}] completed -> {res}")
            except Exception as exc:
                print(f"[{file_name}] thread error -> {exc}")

    summary_lines = []
    summary_lines.append("=== Summary ===")
    for res in sorted(results):
        summary_lines.append(str(res))
    
    
    print("\n" + "\n".join(summary_lines))
    
    summary_file = os.path.join(LOG_FOLDER, "summary.txt")
    with open(summary_file, 'w', encoding='utf-8') as f:
        f.write("\n".join(summary_lines))
    
    print(f"\nSummary saved to: {summary_file}")