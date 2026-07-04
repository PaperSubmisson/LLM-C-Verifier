from pycparser import c_parser, c_ast
import re
import json

def preprocess_code(text):
    text = re.sub(r'/\*.*?\*/', '',text,flags = re.DOTALL)
    text = re.sub(r'//.*','',text)
    text = re.sub(r'__attribute__\s*\(\(.*\)\)', '', text)
    text = re.sub(r'void\s*\*\s*malloc\s*\(.*?\)\s*;', '', text)
    
    text = re.sub(r'\\\r?\n', ' ', text)
    lines = text.split('\n')
    cleaned_lines = []
    in_extern_block = False
    for line in lines:
        stripped = line.strip()
        if stripped.startswith('extern '):
            in_extern_block = True
        
        if not in_extern_block:
            cleaned_lines.append(line)
        
        if in_extern_block and stripped.endswith(';'):
            in_extern_block = False
    text = '\n'.join(cleaned_lines)
    
    lines = text.split('\n')
    new_lines = []
    macros = {} 

    for line in lines:
        stripped = line.strip()
        
        if not stripped:
            continue

        if stripped.startswith('#define'):
            parts = stripped.split()
            if len(parts) >= 3:
                key = parts[1]
                val = " ".join(parts[2:])
                macros[key] = val
            continue 

        if stripped.startswith('#'):
            continue

        if stripped.startswith('extern'):
            continue
        
        for key, val in macros.items():
            pattern = r'\b' + re.escape(key) + r'\b'
            line = re.sub(pattern, lambda m, v=val: v, line)

        new_lines.append(line)

    return '\n'.join(new_lines)

def clean_brackets(expr_str):
    """
    Smart bracket cleanup: repair extra, misplaced, and missing brackets.
    e.g. "(a+b))" -> "(a+b)"
          "Mem[(a+b]" -> "Mem[(a+b)]"
          "((a+b)" -> "((a+b))"
    """
    stack = []
    result = []
    matching_close = {'(': ')', '[': ']', '{': '}'}

    for char in str(expr_str):
        if char in "([{":
            stack.append(char)
            result.append(char)
        elif char in ")]}":
            if not stack:
                continue
            
            top = stack.pop()
            expected_close = matching_close[top]
            
            result.append(expected_close)
        else:
            result.append(char)

    while stack:
        top = stack.pop()
        result.append(matching_close[top])

    return "".join(result)

class AddressTakenVisitor(c_ast.NodeVisitor):
    """
    The escape analyzer traverses the whole AST to identify every variable whose address is taken (e.g., &x). It also enforces scope isolation so that local variables with identical names in different functions are distinguished.
    """
    def __init__(self):
        #  func_name -> set(var_names)
        self.escaped_vars = {'global': set()} 
        self.current_func = 'global'

    def visit_FuncDef(self, node):
        self.current_func = node.decl.name
        self.escaped_vars[self.current_func] = set()
        self.generic_visit(node)
        self.current_func = 'global'

    def visit_UnaryOp(self, node):
        if node.op == '&':
            if isinstance(node.expr, c_ast.ID):
                self.escaped_vars[self.current_func].add(node.expr.name)
        self.generic_visit(node)

class VariableAnalyzer(c_ast.NodeVisitor):
    """
    Scan C AST nodes (typically loop bodies) to analyze read/write liveness of variables. Used to determine in/out parameters for Boogie procedures.
    """
    def __init__(self, global_vars_set, func_params_set, func_locals_set):
        # context information passed in from outside
        self.all_globals = global_vars_set      
        self.func_params = func_params_set      
        self.func_locals = func_locals_set      

        self.reads = set()  
        self.writes = set() 
        self.declares_in_loop = set() 

        # Auxiliary: track variables declared within loop bodies to prevent them from being mistakenly identified as external variables.
        self.current_loop_locals = set()

    def _record_var_access(self, var_name, is_write):
        if var_name in self.all_globals:
            return

        if var_name in self.current_loop_locals:
            return

        if var_name in self.func_params or var_name in self.func_locals:
            if is_write:
                self.writes.add(var_name)
            else:
                self.reads.add(var_name)

    def visit_ID(self, node):
        """Handle standalone variable names (e.g., 'x' in 'if (x < 10)')"""
        # ID node could be an lvalue (write) or an rvalue (read)
        # Here we default to read, because writes are handled specifically in visit_Assignment
        self._record_var_access(node.name, False)

    def visit_Assignment(self, node):
        """Handle assignment statements (x = ...)"""
        # 1. Identify the lvalue (write)
        # We need to recursively strip ArrayRef to get the underlying variable name
        # Example: a[i] = ... → here a is being written
        # Example: m[x][y] = ... → here m is being written
        
        curr = node.lvalue
        while isinstance(curr, c_ast.ArrayRef) or isinstance(curr, c_ast.StructRef):
            if isinstance(curr, c_ast.ArrayRef):
                self.visit(curr.subscript) 
                curr = curr.name
            else:
                curr = curr.name 
            
        if isinstance(curr, c_ast.ID):
            self._record_var_access(curr.name, True)
        
        self.visit(node.rvalue)

    def visit_UnaryOp(self, node):
        if node.op in ['p++', '++', 'p--', '--']:
            curr = node.expr
            
            while isinstance(curr, c_ast.ArrayRef) or isinstance(curr, c_ast.StructRef):
                if isinstance(curr, c_ast.ArrayRef):
                    self.visit(curr.subscript)
                    curr = curr.name
                else:
                    curr = curr.name
            
            if isinstance(curr, c_ast.ID):
                self._record_var_access(curr.name, True)
        
        self.visit(node.expr)

    def visit_Decl(self, node):
        self.declares_in_loop.add(node.name)
        self.current_loop_locals.add(node.name) 
        
        if node.init:
            self.visit(node.init)

    def visit_Return(self, node):
        # Force control-flow variables to be passed as in/out parameters.
        self._record_var_access("result", True)
        self._record_var_access("result", False)
        self._record_var_access("has_returned", True)
        self._record_var_access("has_returned", False)
        if node.expr:
            self.visit(node.expr)
    
    def visit_Goto(self, node):
        """Record the modifications to control‑flow variables made by special Goto statements that jump out of the current main logic."""
        if node.name in ["out", "end", "exit", "done"]:
            self._record_var_access("has_returned", True)
            self._record_var_access("has_returned", False)
    
    def generic_visit(self, node):
        super().generic_visit(node)

class CToBoogieVisitor(c_ast.NodeVisitor):
    def __init__(self,specs_json_str):
        self.smoke_test = False 
        self.func_ret_types = {} 
        self.indent_level = 0
        self.output_global = [] #global variable declaration statements
        self.output = [] #final complete code
        self.boogie_axioms = [] #list for storing axioms and functions
        self.tmp_count = 0  # temporary variable counter

        self.current_decls = [] 
        self.current_stmts = [] 
        self.global_inits = [] 
        self.var_types = {} 
        self.ptr_target_types = {} # Record the pointed‑to type of a pointer (e.g., p → 'real').
        self.snapshot_is_address = set() # Record which snapshot variables represent memory base addresses.
        self.typedef_env = {} # Record typedef alias mappings (e.g., 'size_t' → 'int').
        self.struct_env = {}  # Record struct fields (e.g., 'Point' -> {'x': 'int', 'y': 'real'}).
        self.typedef_is_ptr = set() # Record whether the typedef is a pointer.
        self.all_globals = set()  
        # Register the global memory model.
        self.all_globals.update(["Mem_int", "Mem_real", "Allocator", "Alloc", "Size"])
        self.output_global.extend([
            "var Mem_int: [int]int;    ",
            "var Mem_real:[int]real;  ",
            "var Allocator: int;       ",
            "var Alloc: [int]bool;     ",
            "var Size:[int]int;       "
        ])
        self.var_types.update({
            "Mem_int": "[int]int",
            "Mem_real": "[int]real",
            "Allocator": "int",
            "Alloc": "[int]bool",
            "Size": "[int]int"
        })
        self.current_modifies = set() #Which global variables are modified by the current function
        self.vis_vars = set() # Used to dynamically track live variables within the current scope
        self.loop_counter = 0 
        self.call_counter = 0  
        
        self.extracted_procedures = []

        # Context information within the current function (filled by visit_FuncDef)
        self.current_func_params = set()
        self.current_func_locals = set() 
        self.loop_specs = {}
        self.emitted_safety_checks = set() 
        try:
            if isinstance(specs_json_str, dict):
                raw_map = specs_json_str
            else:
                clean_json = specs_json_str.replace("```json", "").replace("```", "").strip()
                raw_map = json.loads(clean_json)
            
            if "global" in raw_map:
                global_defs = raw_map["global"]
                if isinstance(global_defs, list):
                    self.boogie_axioms = global_defs
                elif isinstance(global_defs, str):
                    self.boogie_axioms = [global_defs]

            for loop_id, specs in raw_map.items():
                if loop_id == "global": 
                    continue
                if specs is None: 
                    specs = {} 
                processed_spec = {
                    "requires": [],
                    "ensures": [],
                    "invariants": []
                }
                for key in ["requires", "ensures", "invariants"]:
                    k_list = specs.get(key, [])
                    if isinstance(k_list, str): k_list = [k_list] 
                    if k_list: 
                        cleaned_list =[clean_brackets(i) for i in k_list]
                        final_list = []
                        for expr in cleaned_list:
                            expr = re.sub(r'(\d+e[+-]?\d+)(?!\.)', r'\1.0', expr)
                            
                            final_list.append(expr)
                        
                        combined_expr = " && ".join([f"({i})" for i in final_list])
                        
                        if "real" in str(self.var_types.values()): 
                            processed_spec[key] = combined_expr.replace('%',' mod ')
                        else:
                            processed_spec[key] = combined_expr.replace('/',' div ').replace('%',' mod ')
                    else:
                        processed_spec[key] = "true"
                self.loop_specs[str(loop_id)] = processed_spec
        except:
            print("JSON parsing failed; default parameter 'true' will be used.")
            self.loop_specs = {}

    def _make_indent(self):
        return '  ' * self.indent_level

    def _emit(self, line):
        self.current_stmts.append(self._make_indent() + line)

    def _resolve_base_type(self, node):
        """Recursively unwrap AST nodes to obtain the underlying C basic type."""
        if isinstance(node, c_ast.IdentifierType):
            name = node.names[0]
            if name in self.typedef_env:
                return self.typedef_env[name]
            if 'void' in node.names:
                return 'void'
            if 'float' in node.names or 'double' in node.names:
                return 'real'
            return 'int'
        
        elif isinstance(node, c_ast.Struct):
            return f"struct {node.name}" if node.name else "struct_anon"
        elif hasattr(node, 'type'):
            return self._resolve_base_type(node.type)
        return 'int'
    
    def _is_pointer_type(self, type_node):
        if isinstance(type_node, c_ast.PtrDecl):
            return True
        if isinstance(type_node, c_ast.TypeDecl) and isinstance(type_node.type, c_ast.IdentifierType):
            name = type_node.type.names[0]
            if name in getattr(self, 'typedef_is_ptr', set()):
                return True
        return False

    def _get_exit_label(self):
        proc_name = getattr(self, "current_proc_name", "default")
        return f"EXIT_{proc_name}"

    def _sizeof(self, type_node):
        if isinstance(type_node, c_ast.ArrayDecl):
            if type_node.dim:
                dim_expr = str(self._visit_expr(type_node.dim))
            else:
                dim_expr = "1"
                
            elem_size_expr = str(self._sizeof(type_node.type))
            
            if elem_size_expr == "1":
                return dim_expr
            elif dim_expr == "1":
                return elem_size_expr
            else:
                return f"({dim_expr} * {elem_size_expr})"
            
        elif self._is_pointer_type(type_node):
            return 1 
        else:
            base = self._resolve_base_type(type_node)
            if base.startswith("struct "):
                struct_name = base.split(" ")[1]
                if struct_name in self.struct_env:
                    return self.struct_env[struct_name]['size']
            return 1 

    def _is_escaped(self, var_name):
        """Determine whether a variable has escaped due to its address being taken (based on precise scope)."""
        if not hasattr(self, 'escaped_vars'):
            return False
            
        # Note: we use original_func_name here, so that even if loop_0 is extracted, we can still look up variables in the original function (e.g., main).
        curr_func = getattr(self, "original_func_name", "global")
        
        if var_name in self.current_func_locals or var_name in self.current_func_params:
            return var_name in self.escaped_vars.get(curr_func, set())
            
        if var_name in self.all_globals:
            return any(var_name in evs for evs in self.escaped_vars.values())
            
        return var_name in self.escaped_vars.get(curr_func, set())

    def _register_struct(self, struct_node):
        if struct_node.decls: 
            struct_name = struct_node.name
            if struct_name and struct_name not in self.struct_env:
                self.struct_env[struct_name] = {'size': 0, 'fields': {}}
                current_offset = 0
                
                for field in struct_node.decls:
                    field_name = field.name
                    field_base_type = self._resolve_base_type(field.type)
                    
                    is_ptr = self._is_pointer_type(field.type)
                    is_arr = isinstance(field.type, c_ast.ArrayDecl)
                    
                    field_size_expr = str(self._sizeof(field.type))
                    try:
                        field_size = eval(field_size_expr)
                    except:
                        field_size = 1 
                    
                    self.struct_env[struct_name]['fields'][field_name] = {
                        'offset': current_offset,
                        'b_type': field_base_type,
                        'is_ptr': is_ptr,  
                        'is_arr': is_arr   
                    }
                    current_offset += field_size 
                    
                self.struct_env[struct_name]['size'] = current_offset

    def _get_boogie_type(self, type_node, var_name=None):
        """Map C type nodes to Boogie types: int, real, [int]int, and [int]real."""
        base = self._resolve_base_type(type_node)

        is_ptr = self._is_pointer_type(type_node)
        is_arr = isinstance(type_node, c_ast.ArrayDecl)
        is_struct = base.startswith("struct ")

        is_escaped = False
        if var_name:
            is_escaped = self._is_escaped(var_name)
        
        if var_name and (is_ptr or is_arr or is_struct or is_escaped):
            if is_arr and isinstance(type_node.type, c_ast.PtrDecl):
                self.ptr_target_types[var_name] = "ptr_to_" + base
            else:
                self.ptr_target_types[var_name] = base
            
        # If it is an array, pointer, or struct instance, it is merely an address (int) in Boogie.
        if is_ptr or is_arr or is_struct or is_escaped:
            return "int"
        else:
            return base

    def _get_struct_name(self, node):
        if isinstance(node, c_ast.ID):
            t = self.ptr_target_types.get(node.name, "")
            if t.startswith("struct "):
                return t.split(" ")[1] 
        elif isinstance(node, c_ast.ArrayRef):
            return self._get_struct_name(node.name)
        elif isinstance(node, c_ast.UnaryOp) and node.op == '*':
            return self._get_struct_name(node.expr)
        
        elif isinstance(node, c_ast.StructRef):
            parent_struct = self._get_struct_name(node.name)
            if parent_struct in self.struct_env and node.field.name in self.struct_env[parent_struct]['fields']:
                b_type = self.struct_env[parent_struct]['fields'][node.field.name]['b_type']
                if b_type.startswith("struct "):
                    return b_type.split(" ")[1]
        return "UNKNOWN_STRUCT"

    def visit_Typedef(self, node):
        if hasattr(node.type, 'type') and isinstance(node.type.type, c_ast.Struct):
            struct_node = node.type.type
            if not struct_node.name:
                struct_node.name = node.name 
            self._register_struct(struct_node)
        
        base_type = self._resolve_base_type(node.type)
        self.typedef_env[node.name] = base_type
        
        if self._is_pointer_type(node.type):
            self.typedef_is_ptr.add(node.name)

    def _is_real_expr(self, expr_str):
        """Lightweight heuristic: check whether the expression string contains real variables or decimal constants."""
        expr_str = str(expr_str)
        if re.search(r'\d+\.\d+', expr_str):
            return True
        if "real(" in expr_str: 
            return True
        words = re.findall(r'\b[a-zA-Z_]\w*\b', expr_str)
        for w in words:
            t = self.var_types.get(w, "int")
            if "real" in t:
                return True
        return False
    
    def _ensure_real_literal(self, expr_str):
        expr_str = str(expr_str)
        
        if re.fullmatch(r'-?\d+', expr_str):
            return f"{expr_str}.0"
        
        if '.' in expr_str or expr_str.startswith("real("):
            return expr_str
            
        words = re.findall(r'\b[a-zA-Z_]\w*\b', expr_str)
        if words:
            all_real = True
            for w in words:
                if w in ["Mem_int", "Mem_real", "Alloc", "Size", "Allocator", "old"]:
                    continue
                t = self.var_types.get(w, "int")
                if "real" not in t:
                    all_real = False
                    break
            if not all_real:
                return f"real({expr_str})"
                
        return expr_str
    
    def _new_temp(self, b_type="int"):
        name = f"t{self.tmp_count}"
        self.tmp_count += 1
        
        self.current_decls.append(f"var {name}: {b_type};")
        self.var_types[name] = b_type 
        return name
    
    def _is_nondet_call(self, node):
        if isinstance(node, c_ast.FuncCall) and isinstance(node.name, c_ast.ID):
            name = node.name.name
            if "nondet" not in name:
                return None
            
            if "float" in name or "double" in name: 
                return 3 # real
            elif "uint" in name or "bool" in name or "uchar" in name or "unsigned" in name:
                return 2 # int >= 0
            else:
                return 1 # int (include nondet_int, nondet_short, nondet_long, nondet_char)
                
        return None

    def visit_FileAST(self, node):
        at_visitor = AddressTakenVisitor()
        at_visitor.visit(node)
        self.escaped_vars = at_visitor.escaped_vars
        
        for ext in node.ext:
            if isinstance(ext, c_ast.FuncDef):
                f_name = ext.decl.name
                try:
                    raw_ret_type_node = ext.decl.type.type
                    f_ret_type = self._get_boogie_type(raw_ret_type_node)
                except:
                    f_ret_type = "int" 
                self.func_ret_types[f_name] = f_ret_type
        for ext in node.ext:
            if isinstance(ext, c_ast.FuncDef):
                self.visit(ext)
            elif isinstance(ext, c_ast.Typedef):  
                self.visit(ext)
            
            elif isinstance(ext, c_ast.Decl):
                if isinstance(ext.type, c_ast.FuncDecl):
                    continue
                
                if isinstance(ext.type, c_ast.Struct):
                    self._register_struct(ext.type)
                
                
                if not ext.name:
                    continue
                
                var_name = ext.name
                is_escaped = self._is_escaped(var_name)
                if var_name in ["true", "false", "result"]:
                    var_name = var_name + "_c" 
                
                self.all_globals.add(var_name)
                
                boogie_type = self._get_boogie_type(ext.type, var_name=var_name)
                self.var_types[var_name] = boogie_type 
                self.output_global.append(f"var {var_name}: {boogie_type};")
                
                base_type = self._resolve_base_type(ext.type)
                is_ptr = self._is_pointer_type(ext.type)
                is_arr = isinstance(ext.type, c_ast.ArrayDecl)
                
                if is_arr or (base_type.startswith("struct ") and not is_ptr) or is_escaped:
                    size_val = self._sizeof(ext.type)
                    
                    self.global_inits.append(f"  {var_name} := Allocator; ")
                    self.global_inits.append(f"  Allocator := Allocator + {size_val};")
                    self.global_inits.append(f"  Alloc[{var_name}] := true;")
                    self.global_inits.append(f"  Size[{var_name}] := {size_val};")
                
                
                if ext.init:
                    
                    val = self._visit_expr(ext.init)
                    if "real" in boogie_type:
                        val = self._ensure_real_literal(val)
                    
                    if is_escaped:
                        mem_map = "Mem_real" if "real" in boogie_type else "Mem_int"
                        self.global_inits.append(f"  {mem_map}[{var_name}] := {val};")
                    else:
                        self.global_inits.append(f"  {var_name} := {val};")

    def visit_FuncDef(self, node):
        self.vis_vars = set()
        
        self.var_types = {k: v for k, v in self.var_types.items() if k in self.all_globals or k.startswith("Struct_")}
        self.ptr_target_types = {k: v for k, v in self.ptr_target_types.items() if k in self.all_globals}
        # =========================================================
        self.current_modifies = set()
        self.current_decls = []
        self.current_stmts = [] 
        self.current_func_params = set()
        self.current_func_locals = set()
        
        func_name = node.decl.name
        
        self.current_proc_name = func_name
        
        self.original_func_name = func_name
        
        ignored_funcs = ["__VERIFIER_assert", "__VERIFIER_error", "reach_error", 
                         "assume_abort_if_not", "__VERIFIER_nondet_int", 
                         "__VERIFIER_nondet_uint", "__VERIFIER_nondet_bool",
                         "printf", "exit", "abort"]
        if func_name in ignored_funcs or func_name.startswith("__VERIFIER_"):
            return

        if func_name == "main":
            
            self._emit("Allocator := 1; // Initialize memory allocator")
            self.current_modifies.add("Allocator")
            for init_stmt in self.global_inits:
                self._emit(init_stmt)
                
                g_name = init_stmt.strip().split(' ')[0]
                g_name = g_name.split('[')[0] 

                if g_name in self.all_globals:
                    self.current_modifies.add(g_name)
        
        params = []
        param_init_stmts = []
        if node.decl.type.args:
            for param in node.decl.type.args.params:
                
                p_name = param.name
                if p_name:
                    self.vis_vars.add(p_name)
                    
                    p_type = self._get_boogie_type(param.type, var_name=p_name)
                    
                    self.var_types[p_name] = p_type
                    self.current_func_params.add(p_name)
                    
                    params.append(f"in_{p_name}: {p_type}")
                    
                    self.current_decls.append(f"var {p_name}: {p_type};")
                    
                    param_init_stmts.append(f"{p_name} := in_{p_name};")
        
        params_str = ", ".join(params)
        
        ret_type = self.func_ret_types.get(func_name, "int")
        is_void = (ret_type == "void")
        
        self.current_func_ret_type = ret_type 

        sig = f"procedure {func_name}({params_str})"
        if not is_void:
            sig += f" returns (result: {ret_type})"

        specs = self.loop_specs.get(func_name, {"requires": "true", "ensures": "true", "invariants": "true"})
        req_str = specs["requires"]
        ens_str = specs["ensures"]
        
        sig += f"\n  requires {req_str};"
        sig += f"\n  ensures {ens_str};"
        self.indent_level += 1
        
        self.current_decls.append("var has_returned: int;")
        self._emit("has_returned := 0;")
        self.current_func_locals.add("has_returned")
        
        if is_void:
            # Even for void, we also add a dummy result to unify the handling of return logic.
            self.current_decls.append("var result: int;")
        self.current_func_locals.add("result")
        
        for stmt in param_init_stmts:
            self._emit(stmt)
        
        self._hook_proc_entry(func_name)
        
        if node.body:
            self.visit(node.body)
        
        self.indent_level -= 1
        
        self._emit(f"{self._get_exit_label()}:")
        self.indent_level += 1
        self._hook_proc_exit(func_name)
        self._emit("return;")
        self.indent_level -= 1

        if self.current_modifies:
            mods = ", ".join(self.current_modifies)
            sig += f"\nmodifies {mods};"
        
        self.output.append(sig)
        self.output.append("{")
        
        for decl in self.current_decls:
            self.output.append("  " + decl)
        
        if self.smoke_test:
            self.output.append("  assert false; // [SMOKE TEST] Check for Vacuous Truth")
        
        for stmt in self.current_stmts:
            self.output.append(stmt)
        self.output.append("}")

    def visit_Decl(self, node):
        if isinstance(node.type, c_ast.Struct):
            self._register_struct(node.type)
            
        if not node.name:
            return
        if not isinstance(node.type, c_ast.FuncDecl):
            if node.name:
                self.vis_vars.add(node.name)
        var_name = node.name
        is_escaped = self._is_escaped(var_name)
        
        if var_name in ["true", "false", "result"]:
             var_name = var_name + "_c"
        
        is_already_declared = var_name in self.current_func_locals
        self.current_func_locals.add(var_name)
        
        boogie_type = self._get_boogie_type(node.type, var_name=var_name) 
            
        self.var_types[var_name] = boogie_type
        
        if not is_already_declared:
            self.current_decls.append(f"var {var_name}: {boogie_type};")

            base_type = self._resolve_base_type(node.type)
            is_ptr = self._is_pointer_type(node.type)
            is_arr = isinstance(node.type, c_ast.ArrayDecl)
            
            if is_arr or (base_type.startswith("struct ") and not is_ptr) or is_escaped:
                size_val = self._sizeof(node.type)
                self._emit(f"{var_name} := Allocator; ")
                self._emit(f"Allocator := Allocator + {size_val};")
                self._emit(f"Alloc[{var_name}] := true;")
                self._emit(f"Size[{var_name}] := {size_val};")
                
                self.current_modifies.update(["Allocator", "Alloc", "Size"])

        if node.init:
            base_type = self._resolve_base_type(node.type)
            
            if base_type.startswith("struct ") and not is_ptr:
                rhs_addr = self._visit_expr(node.init)
                struct_name = base_type.split(" ")[1]
                
                if struct_name in self.struct_env:
                    fields = self.struct_env[struct_name]['fields']
                    for f_name, f_info in fields.items():
                        offset = f_info['offset']
                        b_type = f_info['b_type']
                        mem_map = "Mem_real" if b_type == "real" else "Mem_int"
                        self.current_modifies.add(mem_map)
                        self._emit(f"{mem_map}[{var_name} + {offset}] := {mem_map}[{rhs_addr} + {offset}];")
            else:
                if self._is_nondet_call(node.init) == 1 or self._is_nondet_call(node.init) == 3:
                    self._emit(f"havoc {node.name};")
                elif self._is_nondet_call(node.init) == 2:
                    self._emit(f"havoc {node.name};")
                    self._emit(f"assume {node.name} >= 0;")
                else:
                    # Note: C array initialization like int a[] = {1,2} is complex (InitList).
                    # For simplicity, we currently skip brace-enclosed array initializers and only handle assignments to ordinary variables/pointers.
                    if not isinstance(node.type, c_ast.ArrayDecl):
                        val = self._visit_expr(node.init)
                        if "real" in boogie_type and not self._is_real_expr(val):
                            val = self._ensure_real_literal(val)
                        self._emit(f"{node.name} := {val};")
                        
                        if is_escaped:
                            mem_map = "Mem_real" if "real" in boogie_type else "Mem_int"
                            self._emit(f"{mem_map}[{node.name}] := {val};")
                            self.current_modifies.add(mem_map)
                        else:
                            self._emit(f"{node.name} := {val};")

    def visit_Goto(self, node):
        target_name = node.name.lower()
        
        if "error" in target_name or "fail" in target_name or "abort" in target_name or "_exit" in target_name:
            self._emit("assert false; ")
            self._emit("assume false; // halt execution")
            return
            
        if target_name in ["out", "end", "exit", "done", "quit", "finish", "return", "break_out"]:
            self._emit("has_returned := 1; ")
            self._emit(f"goto {self._get_exit_label()};")
            return
            
        self._emit(f"goto {node.name};")

    def visit_Label(self, node):
        
        self._emit(f"{node.name}:")
        
        if node.stmt:
            self.visit(node.stmt)
        else:
            self._emit("assume true; // dummy statement for label")

    def visit_Assignment(self, node):
        self.emitted_safety_checks.clear()
        
        lhs_type_raw = self._resolve_base_type(node.lvalue)
        
        if lhs_type_raw.startswith("struct "):
            struct_name = lhs_type_raw.split(" ")[1]
            
            lhs_addr = self._visit_expr(node.lvalue)
            rhs_addr = self._visit_expr(node.rvalue)
            
            if struct_name in self.struct_env:
                fields = self.struct_env[struct_name]['fields']
                for f_name, f_info in fields.items():
                    offset = f_info['offset']
                    b_type = f_info['b_type']
                    mem_map = "Mem_real" if b_type == "real" else "Mem_int"
                    
                    self.current_modifies.add(mem_map)
                    
                    self._emit(f"{mem_map}[{lhs_addr} + {offset}] := {mem_map}[{rhs_addr} + {offset}];")
                return 
        
        var_name = None
        if isinstance(node.lvalue, c_ast.ID):
            var_name = node.lvalue.name
        
        if var_name and var_name in self.all_globals:
                self.current_modifies.add(var_name)

        if isinstance(node.rvalue, c_ast.FuncCall):
            
            func_name = ""
            if isinstance(node.rvalue.name, c_ast.ID):
                func_name = node.rvalue.name.name
            
            if "alloc" in func_name:
                lhs = self._visit_expr(node.lvalue)
                
                self.current_modifies.update(["Allocator", "Alloc", "Size"])
                
                map_name = lhs.split('[')[0]
                if map_name.startswith("Mem_"):
                    self.current_modifies.add(map_name)
                
                if func_name == "calloc" and node.rvalue.args and len(node.args.exprs) == 2:
                    arg1 = self._visit_expr(node.rvalue.args.exprs[0])
                    arg2 = self._visit_expr(node.rvalue.args.exprs[1])
                    size_expr = f"({arg1} * {arg2})"
                elif node.rvalue.args:
                    size_expr = self._visit_expr(node.rvalue.args.exprs[0])
                else:
                    size_expr = "1"
                    
                
                target = lhs
                if not isinstance(node.lvalue, c_ast.ID):
                    target = self._new_temp()
                
                self._emit(f"{target} := Allocator; ")
                self._emit(f"Allocator := Allocator + {size_expr};")
                self._emit(f"Alloc[{target}] := true;")
                self._emit(f"Size[{target}] := {size_expr};")
                
                if target != lhs:
                    self._emit(f"{lhs} := {target};")
                return
            
            nondet_type = self._is_nondet_call(node.rvalue)
            if nondet_type:
                
                lhs = self._visit_expr(node.lvalue)
                
                map_name = lhs.split('[')[0]
                if map_name.startswith("Mem_"):
                    self.current_modifies.add(map_name)
                
                b_t = "real" if nondet_type == 3 else "int"
                
                if isinstance(node.lvalue, c_ast.ID):
                    
                    self._emit(f"havoc {lhs};")
                    if nondet_type == 2: # uint
                        self._emit(f"assume {lhs} >= 0;")
                else:
                    temp = self._new_temp(b_type=b_t)
                    self._emit(f"havoc {temp};")
                    if nondet_type == 2: # uint
                        self._emit(f"assume {temp} >= 0;")
                    
                    self._emit(f"{lhs} := {temp};")
                return
            else:
                if func_name not in ["assume_abort_if_not", "reach_error"] or "VERIFIER_" not in func_name:
                    self.current_modifies.update(["Mem_int", "Mem_real", "Allocator", "Alloc", "Size"])
                
                args_str = []
                if node.rvalue.args:
                    for arg in node.rvalue.args.exprs:
                        args_str.append(self._visit_expr(arg))
                
                lhs = self._visit_expr(node.lvalue)
                
                current_call_id = str(self.call_counter)
                self.call_counter += 1
                self._hook_pre_call(current_call_id, func_name)
                
                self._emit(f"call {lhs} := {func_name}({', '.join(args_str)}); // CallID: {current_call_id}")
                self._hook_post_call(current_call_id, func_name, return_var=lhs)
                return
        
        rhs = self._visit_expr(node.rvalue)
        lhs = self._visit_expr(node.lvalue) 
        
        map_name = lhs.split('[')[0]  
        if map_name.startswith("Mem_"):
            self.current_modifies.add(map_name)

        if node.op == '=':
            is_real_lhs = self._is_real_expr(lhs)
            is_real_rhs = self._is_real_expr(rhs)
            if is_real_lhs or is_real_rhs:
                if not is_real_rhs:
                    rhs = self._ensure_real_literal(rhs)
            self._emit(f"{lhs} := {rhs};")
        else:
            math_op = node.op[:-1]
            
            is_real_lhs = self._is_real_expr(lhs)
            is_real_rhs = self._is_real_expr(rhs)
            if is_real_lhs or is_real_rhs:
                if not is_real_rhs:
                    rhs = self._ensure_real_literal(rhs)
                if math_op == '/': math_op = '/' 
            else:
                if math_op == '/': math_op = 'div'
                if math_op == '%': math_op = 'mod'
            
            self._emit(f"{lhs} := ({lhs} {math_op} {rhs});")

    def _ensure_bool(self, node, expr_str):
        if expr_str in ["true", "false"]:
            return expr_str
        
        if expr_str.startswith("(if ") and expr_str.endswith(" then 1 else 0)"):
            return expr_str[4:-15]
        return f"({expr_str} != 0)"
    
    def _visit_expr(self, node):
        if isinstance(node, c_ast.BinaryOp):
            
            left = self._visit_expr(node.left)
            right = self._visit_expr(node.right)
            op = node.op
            is_real_left = self._is_real_expr(left)
            is_real_right = self._is_real_expr(right)
            
            if is_real_left or is_real_right:
                if not is_real_left:
                    left = self._ensure_real_literal(left)
                if not is_real_right:
                    right = self._ensure_real_literal(right)
                if op == '/': op = '/' 
            else:
                if op == '/': op = 'div'
                elif op == '%': op = 'mod'
            
            if op in ['&&','||']:
                left = self._ensure_bool(node.left, left)
                right = self._ensure_bool(node.right, right)
                return f"(if ({left} {op} {right}) then 1 else 0)"
                
            if op in ['<', '>', '<=', '>=', '==', '!=']:
                return f"(if ({left} {op} {right}) then 1 else 0)"
            return f"({left} {op} {right})"
        
        elif isinstance(node, c_ast.Constant):
            val = str(node.value)
            if node.type not in ['float', 'double', 'char', 'string']:
                
                clean_val = val.rstrip('uUlL')
                try:
                    val = str(int(clean_val, 0))
                except ValueError:
                    pass 
            if node.type in ['float', 'double']:
                val = val.rstrip('fFlL')
                if 'e' in val:
                    if '.' not in val.split('e')[0]:
                        val = val.replace('e', '.0e')
                    elif '.' not in val: 
                         val = val + ".0"
                elif '.' not in val:
                    val += '.0'
                if val.endswith('.'):
                    val += '0'
            return val
        elif isinstance(node, c_ast.ID):
            if node.name == "NULL":
                return "0"
            BUILTIN_MACROS = {
                "LARGE_INT": "1000000",
                "MAX_INT": "2147483647",
                "INT_MAX": "2147483647",
                "INT_MIN": "-2147483648",
                "UINT_MAX": "4294967295"
            }
            
            if node.name in BUILTIN_MACROS:
                return BUILTIN_MACROS[node.name]
            var_name = node.name
            
            if self._is_escaped(var_name):
                b_t = self.var_types.get(var_name, "int")
                mem_map = "Mem_real" if "real" in b_t else "Mem_int"
                return f"{mem_map}[{var_name}]"
            
            if var_name in ["true", "false", "result"]:
                var_name = var_name + "_c"
            
            if (var_name not in self.all_globals and 
                var_name not in self.current_func_locals and 
                var_name not in self.current_func_params and
                not var_name.startswith("in_") and
                var_name not in self.var_types):
                
                self.all_globals.add(var_name)
                self.var_types[var_name] = "int"
                self.output_global.append(f"var {var_name}: int;")

            return var_name
        elif isinstance(node, c_ast.Cast):
            return self._visit_expr(node.expr)
        
        elif isinstance(node, c_ast.TernaryOp):
            
            cond_str = self._visit_expr(node.cond)
            cond_str = self._ensure_bool(node.cond, cond_str)
            
            
            iftrue_str = self._visit_expr(node.iftrue)
            iffalse_str = self._visit_expr(node.iffalse)
            
            is_real_t = self._is_real_expr(iftrue_str)
            is_real_f = self._is_real_expr(iffalse_str)
            if is_real_t or is_real_f:
                if not is_real_t: iftrue_str = self._ensure_real_literal(iftrue_str)
                if not is_real_f: iffalse_str = self._ensure_real_literal(iffalse_str)
            
            return f"(if {cond_str} then {iftrue_str} else {iffalse_str})"
        
        elif isinstance(node, c_ast.ArrayRef):
            arr_base = self._visit_expr(node.name)
            subscript = self._visit_expr(node.subscript)
            
            target_type = self.ptr_target_types.get(arr_base, "int")
            
            
            elem_size = 1
            if target_type.startswith("struct "):
                struct_name = target_type.split(" ")[1]
                if struct_name in self.struct_env:
                    elem_size = self.struct_env[struct_name]['size']
            
            addr_expr = f"({arr_base} + {subscript} * {elem_size})" if elem_size > 1 else f"({arr_base} + {subscript})"
            
            if target_type.startswith("struct ") or target_type.startswith("[int]"):
                return addr_expr
            
            safe_null = f"assert {arr_base} > 0; // [Safety] Null pointer deref"
            safe_uaf = f"assert Alloc[{arr_base}] == true; //[Safety] Use-After-Free"
            
            if safe_null not in self.emitted_safety_checks:
                self._emit(safe_null)
                self.emitted_safety_checks.add(safe_null)
            if safe_uaf not in self.emitted_safety_checks:
                self._emit(safe_uaf)
                self.emitted_safety_checks.add(safe_uaf)
            
            safe_bound = f"assert 0 <= {subscript} && {subscript} < Size[{arr_base}]; // [Safety] Buffer Overflow"
            if safe_bound not in self.emitted_safety_checks:
                self._emit(safe_bound)
                self.emitted_safety_checks.add(safe_bound)
            mem_map = "Mem_real" if target_type == "real" else "Mem_int"
            return f"{mem_map}[{addr_expr}]"
        
        elif isinstance(node, c_ast.StructRef):
            base_expr = self._visit_expr(node.name)
            field_name = node.field.name
            struct_name = self._get_struct_name(node.name)
            
            offset = 0
            b_type = "int"
            is_ptr = False  
            is_arr = False  
            if struct_name in self.struct_env and field_name in self.struct_env[struct_name]['fields']:
                field_info = self.struct_env[struct_name]['fields'][field_name]
                offset = field_info['offset']
                b_type = field_info['b_type']
                is_ptr = field_info.get('is_ptr', False) 
                is_arr = field_info.get('is_arr', False) 
            
            
            addr_expr = f"({base_expr} + {offset})" if offset > 0 else base_expr
            
            
            if (b_type.startswith("struct ") and not is_ptr) or is_arr:
                return addr_expr
            
            safe_null = f"assert {base_expr} > 0; // [Safety] Null pointer deref"
            safe_uaf = f"assert Alloc[{base_expr}] == true; //[Safety] Use-After-Free"
            
            if safe_null not in self.emitted_safety_checks:
                self._emit(safe_null)
                self.emitted_safety_checks.add(safe_null)
            if safe_uaf not in self.emitted_safety_checks:
                self._emit(safe_uaf)
                self.emitted_safety_checks.add(safe_uaf)
            mem_map = "Mem_real" if b_type == "real" and not is_ptr else "Mem_int"
            return f"{mem_map}[{addr_expr}]"
        
        elif isinstance(node, c_ast.UnaryOp):
            
            if node.op == 'sizeof':
                return str(self._sizeof(node.expr.type)) if hasattr(node.expr, 'type') else "1"
            
            if node.op == '&':
                operand_expr = self._visit_expr(node.expr)
                
                m = re.match(r'Mem_\w+\[(.*)\]', operand_expr)
                if m:
                    return m.group(1)
                return operand_expr 
            
            if node.op == '*':
                ptr_expr = self._visit_expr(node.expr)
                target_type = self.ptr_target_types.get(ptr_expr, "int")
                
                if target_type.startswith("struct "):
                    return ptr_expr
                    
                mem_map = "Mem_real" if target_type == "real" else "Mem_int"
                
                safe_null = f"assert {ptr_expr} > 0; // [Safety] Null pointer deref"
                safe_uaf = f"assert Alloc[{ptr_expr}] == true; //[Safety] Use-After-Free"
                
                if safe_null not in self.emitted_safety_checks:
                    self._emit(safe_null)
                    self.emitted_safety_checks.add(safe_null)
                if safe_uaf not in self.emitted_safety_checks:
                    self._emit(safe_uaf)
                    self.emitted_safety_checks.add(safe_uaf)
                return f"{mem_map}[{ptr_expr}]"
            
            var_name = self._visit_expr(node.expr) 
            if node.op in ['p++','p--','++','--']:
                if isinstance(node.expr, c_ast.ID):
                    if var_name in self.all_globals:
                        self.current_modifies.add(var_name)

            v_type = self.var_types.get(var_name, "int")
            step = "1.0" if "real" in v_type else "1"
            
            if node.op == 'p++': 
                temp = self._new_temp()     
                self._emit(f"{temp} := {var_name};")     
                self._emit(f"{var_name} := {var_name} + {step};") 
                return temp                
            elif node.op == 'p--':
                temp = self._new_temp()
                self._emit(f"{temp} := {var_name};")
                self._emit(f"{var_name} := {var_name} - {step};")
                return temp
            
            elif node.op == '++':
                self._emit(f"{var_name} := {var_name} + {step};") 
                return var_name             
            elif node.op == '--':
                self._emit(f"{var_name} := {var_name} - {step};") 
                return var_name 
            
           
            elif node.op == '-':
                return f"-{var_name}"
            elif node.op == '!':
                if var_name.startswith("(if ") and var_name.endswith(" then 1 else 0)"):
                    inner = var_name[4:-15]
                    return f"(if (!{inner}) then 1 else 0)"
                else:
                    zero_str = "0.0" if self._is_real_expr(var_name) else "0"
                    return f"(if ({var_name} == {zero_str}) then 1 else 0)"
        
        elif isinstance(node, c_ast.Assignment):
            rhs = self._visit_expr(node.rvalue)
            lhs = self._visit_expr(node.lvalue)
            
           
            map_name = lhs.split('[')[0]
            if map_name.startswith("Mem_") or map_name in self.all_globals:
                self.current_modifies.add(map_name)

           
            if node.op == '=':
                is_real_lhs = self._is_real_expr(lhs)
                is_real_rhs = self._is_real_expr(rhs)
                if is_real_lhs or is_real_rhs:
                    if not is_real_rhs:
                        rhs = self._ensure_real_literal(rhs)
                self._emit(f"{lhs} := {rhs};")
            else:
                math_op = node.op[:-1]
                is_real_lhs = self._is_real_expr(lhs)
                is_real_rhs = self._is_real_expr(rhs)
                if is_real_lhs or is_real_rhs:
                    if not is_real_rhs:
                        rhs = self._ensure_real_literal(rhs)
                    if math_op == '/': math_op = '/' 
                else:
                    if math_op == '/': math_op = 'div'
                    if math_op == '%': math_op = 'mod'
                self._emit(f"{lhs} := ({lhs} {math_op} {rhs});")
            
            
            return lhs
       
        elif isinstance(node, c_ast.FuncCall):
            
            func_name = ""
            if isinstance(node.name, c_ast.ID):
                func_name = node.name.name
            
            nondet_type = self._is_nondet_call(node)
            if nondet_type:
                
                b_t = "real" if nondet_type == 3 else "int"
                temp = self._new_temp(b_type=b_t)

                self._emit(f"havoc {temp};")
                if nondet_type == 2: self._emit(f"assume {temp} >= 0;")
                return temp
            elif "alloc" in func_name:
                if func_name == "calloc" and node.args and len(node.args.exprs) == 2:
                    arg1 = self._visit_expr(node.args.exprs[0])
                    arg2 = self._visit_expr(node.args.exprs[1])
                    size_expr = f"({arg1} * {arg2})"
                elif node.args:
                    size_expr = self._visit_expr(node.args.exprs[0])
                else:
                    size_expr = "1"
                    
                self.current_modifies.update(["Allocator", "Alloc", "Size"])
                
                temp = self._new_temp()
                self._emit(f"{temp} := Allocator; ")
                self._emit(f"Allocator := Allocator + {size_expr};")
                self._emit(f"Alloc[{temp}] := true;")
                self._emit(f"Size[{temp}] := {size_expr};")
                return temp
            else:
                
                if func_name not in ["assume_abort_if_not", "reach_error"] or "VERIFIER_" not in func_name:
                    self.current_modifies.update(["Mem_int", "Mem_real", "Allocator", "Alloc", "Size"])
                
                args_str = []
                if node.args:
                    for arg in node.args.exprs:
                        args_str.append(self._visit_expr(arg))
                
               
                func_name = node.name.name if isinstance(node.name, c_ast.ID) else ""
                actual_ret_type = self.func_ret_types.get(func_name, "int")
                
                ret_temp = self._new_temp(b_type=actual_ret_type)
                current_call_id = str(self.call_counter)
                self.call_counter += 1
            
                self._hook_pre_call(current_call_id, func_name)
               
                self._emit(f"call {ret_temp} := {func_name}({', '.join(args_str)}); // CallID: {current_call_id}")
                self._hook_post_call(current_call_id, func_name, return_var=ret_temp)
                
                return ret_temp
        
        return "UNKNOWN"
    
    def visit_UnaryOp(self, node):
        var_name = self._visit_expr(node.expr)
        
        if node.op in ['p++', 'p--', '++', '--']:
            if isinstance(node.expr, c_ast.ID):
                if var_name in self.all_globals:
                    self.current_modifies.add(var_name)
                    
            v_type = self.var_types.get(var_name, "int")
            step = "1.0" if "real" in v_type else "1"

            if node.op in ['p++', '++']:
                self._emit(f"{var_name} := {var_name} + {step};")
            elif node.op in ['p--', '--']:
                self._emit(f"{var_name} := {var_name} - {step};")

    def visit_Break(self, node):
        self._emit("break;")

    def visit_If(self, node):
        self.emitted_safety_checks.clear()
        cond_str = self._visit_expr(node.cond)
        cond_str = self._ensure_bool(node.cond, cond_str)

        self._emit(f"if ({cond_str})")
        self._emit("{")
        self.indent_level += 1
        if node.iftrue:
            self.visit(node.iftrue)
        self.indent_level -= 1
        self._emit("}")

        if node.iffalse:
            self._emit("else")
            self._emit("{")
            self.indent_level += 1
            self.visit(node.iffalse)
            self.indent_level -= 1
            self._emit("}")
    
    def visit_While(self, node):
        self.emitted_safety_checks.clear()
        analyzer = VariableAnalyzer(
            self.all_globals, 
            self.current_func_params, 
            self.current_func_locals
        )
        
        analyzer.visit(node)
        
        actual_writes = analyzer.writes.copy()
        if "has_returned" in actual_writes:
            actual_writes.add("result") 
            
        inputs = sorted(list(analyzer.reads | actual_writes))
        outputs = sorted(list(actual_writes)) 
        
        visible_vars = analyzer.reads.union(analyzer.writes)
        inputs = sorted(list(analyzer.reads | analyzer.writes))
       
        outputs = sorted(list(analyzer.writes))
        
        main_stmts = self.current_stmts
        main_decls = self.current_decls
        main_modifies = self.current_modifies
        main_vis_vars = self.vis_vars.copy()               
        main_func_locals = self.current_func_locals.copy() 
        main_proc_name = getattr(self, "current_proc_name", "default") 
        
        proc_stmts = []
        proc_decls = []
        proc_modifies = set()
        
        self.current_stmts = proc_stmts
        self.current_decls = proc_decls
        self.current_modifies = proc_modifies
        
        self.vis_vars = set(inputs)
        
        self.current_func_locals = set(inputs)
        
        current_id = str(self.loop_counter)
        self.loop_counter += 1
        proc_name = f"loop_{current_id}"
        self.current_proc_name = proc_name 
        specs = self.loop_specs.get(f"loop_{current_id}", {"requires": "true", "ensures": "true", "invariants": "true"})
        req_str = specs["requires"]
        ens_str = specs["ensures"]
        inv_str = specs["invariants"]
        
        original_stmts = self.current_stmts
        
        captured_stmts = []
        self.current_stmts = captured_stmts
        cond_str = self._visit_expr(node.cond)
        cond_str = self._ensure_bool(node.cond, cond_str)
        
        self.current_stmts = original_stmts
        
        for stmt in captured_stmts:
            self._emit(stmt.strip())
        self._hook_insert_snap_entry(current_id,visible_vars) 
        
        self._emit(f"while ({cond_str})")
        self._emit(f"invariant {inv_str};")
        self._emit("{")
        self.indent_level += 1
        self._hook_insert_snap_head(current_id,visible_vars)
        
        if node.stmt:
            self.visit(node.stmt)

        
        for stmt in captured_stmts:
            self._emit(stmt.strip())
        
        self._hook_insert_snap_body(current_id,visible_vars)
        self.indent_level -= 1
        self._emit("}")
        self._hook_insert_snap_done(current_id,visible_vars)
        
        
        self.current_stmts = main_stmts
        self.current_decls = main_decls
        self.current_modifies = main_modifies
        self.vis_vars = main_vis_vars                      
        self.current_func_locals = main_func_locals        
        self.current_proc_name = main_proc_name            
        
        in_params_list = []
        for v in inputs:
            v_type = self.var_types.get(v, "int")
            in_params_list.append(f"in_{v}: {v_type}")
        in_params_str = ", ".join(in_params_list)

        out_params_list = []
        for v in outputs:
            v_type = self.var_types.get(v, "int")
            out_params_list.append(f"{v}: {v_type}")
        out_params_str = ", ".join(out_params_list)
        
        init_shadow_vars = []
        for v in inputs:
            init_shadow_vars.append(f"  {v} := in_{v};")
            if v not in outputs:
                v_type = self.var_types.get(v, "int")
                
                proc_decls.append(f"var {v}: {v_type};")
        
        modifies_str = ""
        if proc_modifies:
            modifies_str = f"modifies {', '.join(sorted(proc_modifies))};"
            
            self.current_modifies.update(proc_modifies)
       
        if "has_returned" in outputs:
            proc_stmts.append(f"EXIT_{proc_name}:") 
            proc_stmts.append("  return;")
        
        smoke_str = "  assert false; // [SMOKE TEST] Check for Vacuous Truth\n" if self.smoke_test else "" 
        
        proc_code = f"""
procedure {proc_name}({in_params_str}) returns ({out_params_str})
  {modifies_str}
  requires {req_str}; 
  ensures {ens_str};
{{
{chr(10).join(["  " + d for d in proc_decls])}

{smoke_str}{chr(10).join(init_shadow_vars)}

{chr(10).join(proc_stmts)}
}}
"""
        self.extracted_procedures.append(proc_code)
        
        
        args = ", ".join(inputs)
        rets = ", ".join(outputs)
        self._hook_insert_snap_call(current_id,visible_vars)
        if rets:
            self._emit(f"call {rets} := {proc_name}({args});")
        else:
            self._emit(f"call {proc_name}({args});")
        self._hook_insert_snap_called(current_id,visible_vars)
       
        if "has_returned" in outputs:
            self._emit("if ((has_returned == 1))")
            self._emit("{")
            self.indent_level += 1
            self._emit(f"goto {self._get_exit_label()};")
            self.indent_level -= 1
            self._emit("}")
        
    def _hook_insert_snap_call(self,current_id,visible_vars):
        pass
    def _hook_insert_snap_called(self,current_id,visible_vars):
        pass
    def _hook_insert_snap_entry(self,current_id,visible_vars):
        pass
    def _hook_insert_snap_head(self,current_id,visible_vars):
        pass
    def _hook_insert_snap_body(self,current_id,visible_vars):
        pass
    def _hook_insert_snap_done(self,current_id,visible_vars):
        pass

    def visit_For(self, node):
        if node.init:
            self.visit(node.init)

        new_block_items = []
        
        if node.stmt:
            if isinstance(node.stmt, c_ast.Compound):
                if node.stmt.block_items:
                    new_block_items.extend(node.stmt.block_items)
            else:
                new_block_items.append(node.stmt)
        
        if node.next:
            new_block_items.append(node.next)
          
        new_body = c_ast.Compound(block_items=new_block_items, coord=node.coord)
        
        new_cond = node.cond if node.cond else c_ast.Constant(type='int', value='1')
        
        fake_while_node = c_ast.While(cond=new_cond, stmt=new_body, coord=node.coord)
        
        self.visit_While(fake_while_node)

    def visit_FuncCall(self, node):
        self.emitted_safety_checks.clear()
        func_name = ""
        
        if isinstance(node.name, c_ast.ID):
            func_name = node.name.name
        
        if func_name not in ["__VERIFIER_assert", "assume_abort_if_not", "reach_error"]:
            self.current_modifies.update(["Mem_int", "Mem_real", "Allocator", "Alloc", "Size"])
        args_nodes = [] 
        args_str = []   
        if node.args:
            for arg in node.args.exprs:
                args_nodes.append(arg)
                args_str.append(self._visit_expr(arg))

        if func_name in ["__VERIFIER_assert", "___SL_ASSERT"]:
            
            if args_nodes:
                cond = self._ensure_bool(args_nodes[0], args_str[0])
                self._emit(f"assert {cond};")
            else:
                self._emit("assert true;") 

        elif func_name == "assume_abort_if_not":
            
            if args_nodes:
                cond = self._ensure_bool(args_nodes[0], args_str[0])
                self._emit(f"assume {cond};")
            
        
        elif func_name == "__VERIFIER_error" or func_name == "reach_error":
            
            self._emit("assert false;")
        
        elif func_name in ["abort", "exit"]:
            self._emit("assume false; // halt execution")
            return
        
        elif func_name == "free":
            if args_str:
                ptr_expr = args_str[0]
                self.current_modifies.add("Alloc")
                self._emit(f"assert {ptr_expr} > 0; // [Safety] Free Non-null")
                self._emit(f"assert Alloc[{ptr_expr}] == true; // [Safety] Prevent Double Free")
                self._emit(f"Alloc[{ptr_expr}] := false;")
            return
        
        
        else:
            args_joined = ", ".join(args_str)
            current_call_id = str(self.call_counter)
            self.call_counter += 1

            self._hook_pre_call(current_call_id, func_name)
            ret_type = self.func_ret_types.get(func_name, "void")
            
            if ret_type != "void":
                
                dummy_temp = self._new_temp(b_type=ret_type)
                self._emit(f"call {dummy_temp} := {func_name}({args_joined}); // CallID: {current_call_id} (Return Discarded)")
                self._hook_post_call(current_call_id, func_name, return_var=dummy_temp)
            else:
                
                self._emit(f"call {func_name}({args_joined}); // CallID: {current_call_id}")
                self._hook_post_call(current_call_id, func_name)
    
    def _hook_proc_entry(self, proc_name): pass
    def _hook_proc_exit(self, proc_name): pass
    def _hook_pre_call(self, call_id, callee_name): pass
    def _hook_post_call(self, call_id, callee_name, return_var=None): pass

    def visit_Return(self, node):
        self.emitted_safety_checks.clear() 
        if node.expr:
            val = self._visit_expr(node.expr)
            if getattr(self, "current_func_ret_type", "int") == "real":
                if not self._is_real_expr(val):
                    val = self._ensure_real_literal(val)
            self._emit(f"result := {val};")
        
        self._emit("has_returned := 1;")
        self._emit(f"goto {self._get_exit_label()};")

    def get_code(self):
        axioms_code = "\n".join(self.boogie_axioms)

        global_code = "\n".join(self.output_global)
        
        procs_code = "\n".join(self.extracted_procedures)
        
        main_code = "\n".join(self.output)
        
        return axioms_code + "\n"+global_code + "\n" + procs_code + "\n" + main_code


class SnapshotInserter(CToBoogieVisitor):
    def __init__(self, invariants_json):
        
        super().__init__(invariants_json)
        
        self.nondet_counter = 0
    
    def _add_snapshot(self, target_var):
        
        snap_name = f"snap_nondet_{self.nondet_counter}"
        self.nondet_counter += 1
        
        v_type = self.var_types.get(target_var, "int")
        
        self.current_decls.append(f"var {snap_name}: {v_type};")
        
        zero_str = "0.0" if v_type == "real" else "0"
        self._emit(f"{snap_name} := {target_var} + {zero_str};")

    def visit_While(self, node):
        analyzer = VariableAnalyzer(
            self.all_globals, 
            self.current_func_params, 
            self.current_func_locals
        )
        analyzer.visit(node)
        
        active_vars = sorted(list(analyzer.reads | analyzer.writes))
        
        current_id = str(self.loop_counter)
        self.loop_counter += 1

        specs = self.loop_specs.get(f"loop_{current_id}", {"requires": "true", "ensures": "true", "invariants": "true"})
        inv_str = specs["invariants"]
        
        for var in active_vars:
            shadow_name = f"in_{var}"
            
            if f"in_{var}" in inv_str:
                v_type = self.var_types.get(var, "int")
                self.current_decls.append(f"var {shadow_name}: {v_type};")
                
                self._emit(f"{shadow_name} := {var};")
        
        original_stmts = self.current_stmts
        
        captured_stmts = []
        self.current_stmts = captured_stmts
        cond_str = self._visit_expr(node.cond)
        cond_str = self._ensure_bool(node.cond, cond_str)
        
        self.current_stmts = original_stmts
        
        for stmt in captured_stmts:
            self._emit(stmt.strip())
        
        self._emit(f"while ({cond_str})")
        self._emit(f"invariant {inv_str};")
        self._emit("{")
        self.indent_level += 1
        
        if node.stmt:
            self.visit(node.stmt)

        for stmt in captured_stmts:
            self._emit(stmt.strip())
        
        self.indent_level -= 1
        self._emit("}")
        
        
    def visit_Decl(self, node):
        super().visit_Decl(node)
        
        if node.init and self._is_nondet_call(node.init):
            self._add_snapshot(node.name)
    
    def visit_Assignment(self, node):
        super().visit_Assignment(node)
        
        if node.op == '=':
            if isinstance(node.rvalue, c_ast.FuncCall):
                if self._is_nondet_call(node.rvalue):
                    if isinstance(node.lvalue, c_ast.ID):
                        self._add_snapshot(node.lvalue.name)
    
    def _visit_expr(self, node):
        result_str = super()._visit_expr(node)
        
        if isinstance(node, c_ast.FuncCall):
            if self._is_nondet_call(node):
                self._add_snapshot(result_str)
        
        return result_str

class FullSnapshotInserter(CToBoogieVisitor):
    def __init__(self, invariants_json):
        super().__init__(invariants_json)
        self.assertion_counter = 0

    def _take_snapshot(self, prefix,visible_vars, extra_vars=None):
        all_vars = visible_vars.union(self.all_globals)
        if extra_vars:
            if isinstance(extra_vars, str):
                if re.match(r'^[a-zA-Z_]\w*$', extra_vars):
                    all_vars.add(extra_vars)
            else:
                for v in extra_vars:
                    if re.match(r'^[a-zA-Z_]\w*$', v):
                        all_vars.add(v)

        for var_name in sorted(list(all_vars)):
            snap_name = f"{prefix}_{var_name}"
            query_name = var_name[3:] if var_name.startswith("in_") else var_name
            if query_name in self.ptr_target_types:
                self.snapshot_is_address.add(snap_name)
           
            v_type = self.var_types.get(var_name, "int")
            if v_type.startswith("[int]"):
                self.current_decls.append(f"var {snap_name}: {v_type};")
                
                self._emit(f"havoc {snap_name};")
                self._emit(f"assume {snap_name} == {var_name};")
            else:
                self.current_decls.append(f"var {snap_name}: {v_type};")
                
                zero_str = "0.0" if v_type == "real" else "0"
                self._emit(f"{snap_name} := {var_name} + {zero_str};")

    def _hook_insert_snap_call(self,current_id,visible_vars):
        self._take_snapshot(f"snap_loop_{current_id}_call",visible_vars)
    def _hook_insert_snap_called(self,current_id,visible_vars):
        self._take_snapshot(f"snap_loop_{current_id}_called",visible_vars)
    def _hook_insert_snap_entry(self,current_id,visible_vars):
        self._take_snapshot(f"snap_loop{current_id}_entry",visible_vars)
    def _hook_insert_snap_head(self,current_id,visible_vars):
        self._take_snapshot(f"snap_loop{current_id}_head",visible_vars)
    def _hook_insert_snap_body(self,current_id,visible_vars):
        self._take_snapshot(f"snap_loop{current_id}_body",visible_vars)
    def _hook_insert_snap_done(self,current_id,visible_vars):
        self._take_snapshot(f"snap_loop{current_id}_done",visible_vars)
    def _hook_proc_entry(self, proc_name): 
        self._take_snapshot(f"snap_{proc_name}_entry", self.vis_vars)
    def _hook_proc_exit(self, proc_name):
        self._take_snapshot(f"snap_{proc_name}_exit", self.vis_vars)
    def _hook_pre_call(self, call_id, callee_name):
        self._take_snapshot(f"snap_call_{call_id}_pre", self.vis_vars)
    def _hook_post_call(self, call_id, callee_name, return_var=None):
        self._take_snapshot(f"snap_call_{call_id}_post", self.vis_vars,extra_vars=return_var)

    def visit_FuncCall(self, node):
        func_name = ""
        if isinstance(node.name, c_ast.ID):
            func_name = node.name.name
         
        if func_name == "__VERIFIER_assert":
            analyzer = VariableAnalyzer(
                self.all_globals, 
                self.current_func_params, 
                self.current_func_locals
            )
            
            analyzer.visit(node)
            
            visible_vars = analyzer.reads.union(analyzer.writes)
            self._take_snapshot(f"snap_assertion{self.assertion_counter}",visible_vars)
            self.assertion_counter += 1
            
        super().visit_FuncCall(node)

def trans_c_to_boogie(ast, invariants, smoke_test=False):
    translator = CToBoogieVisitor(invariants)
    translator.smoke_test = smoke_test 
    translator.visit(ast)
    return translator.get_code(), translator.var_types, translator.snapshot_is_address, translator.struct_env

def insert_inv_to_boogie_with_snap(ast, invariants):
    
    translator = SnapshotInserter(invariants)
    translator.visit(ast)
    return translator.get_code(), translator.var_types, translator.snapshot_is_address, translator.struct_env

def insert_inv_to_boogie_FULLSNAP(ast, invariants):
    translator = FullSnapshotInserter(invariants)
    translator.visit(ast)
    return translator.get_code(), translator.var_types, translator.snapshot_is_address, translator.struct_env
# --- test code ---
if __name__ == "__main__":
    c_code = """
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "struct_test.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

typedef struct {
    int x;
    int y;
} Point;

int main() {
    int a[10];
    int b[10];
    a[3] = 5;
    return 0;
}
    """
    c_code = preprocess_code(c_code)
    parser = c_parser.CParser()
    ast = parser.parse(c_code)
    response = {
  
}
    result,_,_,_ = trans_c_to_boogie(ast, response, False)
    result2,_,_,_ = insert_inv_to_boogie_FULLSNAP(ast, response)
    print("===  (Boogie) ===")
    print(result)