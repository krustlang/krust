import gc
import re
import sys
import os
import ctypes
import json as json_module
import time
import threading
import hashlib
import argparse
import platform
import requests
import urllib.parse

VERSION = '1.0.0'

# Отключаем сборщик мусора Python
gc.disable()

# ==========================================
# Исключения с поддержкой Traceback
# ==========================================
class KrustError(Exception):
    """Специальное исключение для сохранения стека вызовов"""
    def __init__(self, message, frame=None):
        super().__init__(message)
        self.frames = [frame] if frame else []

    def add_frame(self, frame):
        self.frames.append(frame)

    def __str__(self):
        trace = "\n".join([f"  в {frame}" for frame in reversed(self.frames)])
        return f"[KRUST ERROR] {self.args[0]}\nTraceback (последний вызов внизу):\n{trace}"

# ==========================================
# 1. Лексический анализатор
# ==========================================
TOKEN_SPEC = [
    ('COMMENT', r'//[^\n]*'),
    ('ARROW',   r'=>'),
    ('LPAREN',  r'\('),
    ('RPAREN',  r'\)'),
    ('LBRACKET',r'\['),
    ('RBRACKET',r'\]'),
    ('LBRACE',  r'\{'),
    ('RBRACE',  r'\}'),
    ('COMMA',   r','),
    ('COLON',   r':'),
    ('STRING',  r'"[^"\\]*(?:\\.[^"\\]*)*"'),
    ('BOOL',    r'\b(true|false)\b'),
    ('NUMBER',  r'-?\d+(\.\d+)?'),
    ('IDENT',   r'[a-zA-Z_][a-zA-Z0-9_]*'),
    ('PLUS',    r'\+'),
    ('MINUS',   r'-'),
    ('MUL',     r'\*'),
    ('DIV',     r'/'),
    ('MOD',     r'%'),
    ('EQ',      r'=='),
    ('NEQ',     r'!='),
    ('LTE',     r'<='),
    ('GTE',     r'>='),
    ('LT',      r'<'),
    ('GT',      r'>'),
    ('SKIP',    r'[ \t\r\n]+'),
    ('MISMATCH',r'.'),
]
TOKEN_REGEX = '|'.join(f'(?P<{pair[0]}>{pair[1]})' for pair in TOKEN_SPEC)

OPERATOR_MAP = {
    'PLUS': '+', 'MINUS': '-', 'MUL': '*', 'DIV': '/', 'MOD': '%',
    'EQ': '==', 'NEQ': '!=', 'LT': '<', 'GT': '>', 'LTE': '<=', 'GTE': '>='
}

def tokenize(code):
    tokens = []
    for mo in re.finditer(TOKEN_REGEX, code):
        kind = mo.lastgroup
        value = mo.group()
        if kind == 'NUMBER':
            value = float(value) if '.' in value else int(value)
        elif kind == 'STRING':
            value = value[1:-1]
            value = value.replace('\\n', '\n')
            value = value.replace('\\t', '\t')
            value = value.replace('\\r', '\r')
            value = value.replace('\\033', '\033')
            value = value.replace('\\x1b', '\x1b')
        elif kind in ('SKIP', 'COMMENT') or kind is None:
            continue
        elif kind in OPERATOR_MAP:
            tokens.append(('IDENT', OPERATOR_MAP[kind]))
            continue
        elif kind == 'MISMATCH':
            raise RuntimeError(f'Недопустимый символ: {value}')
        tokens.append((kind, value))
    tokens.append(('EOF', None))
    return tokens

# ==========================================
# 2. Парсер
# ==========================================
VALID_TYPES = {'String', 'Int', 'Float', 'Bool', 'Void', 'Tuple', 'List', 'Json', 'Ref'}

def peek(tokens, offset=0):
    if offset < len(tokens): return tokens[offset]
    return ('EOF', None)

def expect(tokens, kind):
    if tokens[0][0] != kind:
        raise SyntaxError(f"Ожидалось {kind}, получено {tokens[0]}")
    return tokens.pop(0)

def parse_primary(tokens):
    first = tokens[0]
    if first[0] == 'STRING': tokens.pop(0); return ('StringLit', first[1])
    if first[0] == 'NUMBER': tokens.pop(0); return ('IntLit', first[1]) if isinstance(first[1], int) else ('FloatLit', first[1])
    if first[0] == 'BOOL': tokens.pop(0); return ('BoolLit', first[1] == 'true')
    
    if first[0] == 'LBRACKET':
        tokens.pop(0)
        items = []
        while tokens[0][0] != 'RBRACKET':
            items.append(parse_expr(tokens))
            if tokens[0][0] == 'COMMA': tokens.pop(0)
        expect(tokens, 'RBRACKET'); return ('ListLit', items)
        
    if first[0] == 'LBRACE':
        tokens.pop(0)
        pairs = []
        while tokens[0][0] != 'RBRACE':
            key = expect(tokens, 'STRING')[1]; expect(tokens, 'COLON')
            value = parse_expr(tokens)
            pairs.append((key, value))
            if tokens[0][0] == 'COMMA': tokens.pop(0)
        expect(tokens, 'RBRACE'); return ('JsonLit', pairs)
        
    if first[0] == 'IDENT':
        tokens.pop(0); return ('Ident', first[1])
        
    raise SyntaxError(f"Неожиданный токен в primary: {first}")

def parse_expr(tokens):
    first = tokens[0]
    if first[0] == 'LPAREN':
        second = peek(tokens, 1)
        if second[0] == 'IDENT' and second[1] == 'func': return parse_func_def(tokens)
        if second[0] == 'IDENT' and second[1] in VALID_TYPES: return parse_var_decl(tokens)
        if second[0] == 'IDENT' and second[1] == 'return': return parse_return(tokens)
        if second[0] == 'IDENT' and second[1] == 'if': return parse_if(tokens)
        if second[0] == 'IDENT' and second[1] == 'for': return parse_for(tokens)
        if second[0] == 'IDENT' and second[1] == 'while': return parse_while(tokens)
        if second[0] == 'IDENT': return parse_func_call(tokens)
        if second[0] in ('NUMBER', 'STRING', 'BOOL', 'LBRACKET', 'LBRACE', 'LPAREN'): return parse_tuple(tokens)
        raise SyntaxError(f"Неизвестная конструкция после (: second={second}")
    return parse_primary(tokens)

def parse_func_def(tokens):
    expect(tokens, 'LPAREN'); expect(tokens, 'IDENT')
    name = expect(tokens, 'IDENT')[1]; expect(tokens, 'COMMA')
    expect(tokens, 'LPAREN')
    params = []
    while tokens[0][0] != 'RPAREN':
        params.append(expect(tokens, 'IDENT')[1])
        if tokens[0][0] == 'COMMA': tokens.pop(0)
    expect(tokens, 'RPAREN'); expect(tokens, 'ARROW')
    body = parse_block(tokens); expect(tokens, 'RPAREN')
    return ('FuncDef', name, params, body)

def parse_var_decl(tokens):
    expect(tokens, 'LPAREN')
    type_name = expect(tokens, 'IDENT')[1]
    var_name = expect(tokens, 'IDENT')[1]
    expect(tokens, 'ARROW')
    value = parse_expr(tokens)
    expect(tokens, 'RPAREN')
    return ('VarDecl', type_name, var_name, value)

def parse_return(tokens):
    expect(tokens, 'LPAREN'); expect(tokens, 'IDENT'); expect(tokens, 'COMMA')
    value = parse_expr(tokens); expect(tokens, 'RPAREN')
    return ('Return', value)

def parse_if(tokens):
    expect(tokens, 'LPAREN')
    expect(tokens, 'IDENT')
    expect(tokens, 'COMMA')
    condition = parse_expr(tokens)
    expect(tokens, 'COMMA')
    true_block = parse_block(tokens)
    expect(tokens, 'RPAREN')
    return ('If', condition, true_block)

def parse_for(tokens):
    expect(tokens, 'LPAREN')
    expect(tokens, 'IDENT')
    expect(tokens, 'COMMA')
    var_name = expect(tokens, 'IDENT')[1]
    expect(tokens, 'COMMA')
    iterable = parse_expr(tokens)
    expect(tokens, 'COMMA')
    body = parse_block(tokens)
    expect(tokens, 'RPAREN')
    return ('For', var_name, iterable, body)

def parse_while(tokens):
    expect(tokens, 'LPAREN')
    expect(tokens, 'IDENT')
    expect(tokens, 'COMMA')
    condition = parse_expr(tokens)
    expect(tokens, 'COMMA')
    body = parse_block(tokens)
    expect(tokens, 'RPAREN')
    return ('While', condition, body)

def parse_func_call(tokens):
    expect(tokens, 'LPAREN')
    func_name = expect(tokens, 'IDENT')[1]
    args = []
    while tokens[0][0] != 'RPAREN':
        expect(tokens, 'COMMA')
        args.append(parse_expr(tokens))
    expect(tokens, 'RPAREN')
    return ('FuncCall', func_name, args)

def parse_tuple(tokens):
    expect(tokens, 'LPAREN')
    items = []
    items.append(parse_expr(tokens))
    while tokens[0][0] == 'COMMA':
        tokens.pop(0)
        if tokens[0][0] == 'RPAREN': break
        items.append(parse_expr(tokens))
    expect(tokens, 'RPAREN')
    return ('TupleLit', items)

def parse_block(tokens):
    expect(tokens, 'LPAREN')
    stmts = []
    while tokens[0][0] != 'RPAREN':
        stmts.append(parse_expr(tokens))
    expect(tokens, 'RPAREN')
    return ('Block', stmts)

def parse(code):
    tokens = tokenize(code)
    ast = []
    while tokens[0][0] != 'EOF':
        ast.append(parse_expr(tokens))
    return ast

# ==========================================
# 3. Менеджер памяти и Окружение
# ==========================================
class MemoryManager:
    def __init__(self):
        self.allocated = set()
        self.lock = threading.Lock()

    def alloc(self, name):
        with self.lock:
            self.allocated.add(name)

    def free(self, name):
        with self.lock:
            if name in self.allocated:
                self.allocated.remove(name)
            else:
                raise RuntimeError(f"Ошибка памяти: переменная '{name}' не была аллоцирована")

class Environment:
    def __init__(self, parent=None):
        self.vars = {}
        self.funcs = {}
        self.parent = parent
        self.memory = parent.memory if parent else MemoryManager()

    def get(self, name):
        if name in self.vars: return self.vars[name]
        if self.parent: return self.parent.get(name)
        raise RuntimeError(f"Переменная '{name}' не найдена")

    def set(self, name, value): self.vars[name] = value
    
    def update(self, name, value):
        if name in self.vars:
            self.vars[name] = value
        elif self.parent:
            self.parent.update(name, value)
        else:
            raise RuntimeError(f"Переменная '{name}' не найдена для обновления")
    
    def get_func(self, name):
        if name in self.funcs: return self.funcs[name]
        if self.parent: return self.parent.get_func(name)
        return None
        
    def set_func(self, name, data): self.funcs[name] = data
    
    def free_var(self, name):
        if name in self.vars:
            del self.vars[name]
            self.memory.free(name)

# ==========================================
# 4. Встроенные функции и МОСТ PYTHON-KRUST
# ==========================================
BUILTINS = {}

def krust_builtin(name):
    def decorator(func):
        BUILTINS[name] = func
        return func
    return decorator

class ReturnException(Exception):
    def __init__(self, value): self.value = value

class BreakException(Exception): pass
class ContinueException(Exception): pass

def interpolate_string(s, env):
    def replacer(match):
        var_name = match.group(1)
        _, val = env.get(var_name)
        return str(val)
    return re.sub(r'%([a-zA-Z_][a-zA-Z0-9_]*)', replacer, s)

GLOBAL_KRUST_ENV = None

def krust_invoke_from_python(func_name, *args):
    if GLOBAL_KRUST_ENV is None:
        raise RuntimeError("Krust Environment not initialized")
    func_data = GLOBAL_KRUST_ENV.get_func(func_name)
    if not func_data:
        raise RuntimeError(f"Krust function '{func_name}' not found")
    
    params, body, closure_env = func_data
    new_env = Environment(closure_env)
    
    for i, p in enumerate(params):
        if i < len(args):
            py_val = args[i]
            if isinstance(py_val, str): krust_val = ('String', py_val)
            elif isinstance(py_val, bool): krust_val = ('Bool', py_val)
            elif isinstance(py_val, int): krust_val = ('Int', py_val)
            elif isinstance(py_val, float): krust_val = ('Float', py_val)
            else: krust_val = ('String', str(py_val))
            new_env.set(p, krust_val)
    
    try:
        result = evaluate(body, new_env, f"функции '{func_name}' (из Python)")
        return result[1]
    except ReturnException as e:
        return e.value[1]
    except KrustError:
        raise
    except Exception as e:
        raise KrustError(str(e), f"функции '{func_name}' (из Python)")

@krust_builtin("print")
def builtin_print(env, args):
    if len(args) != 1: raise RuntimeError("print принимает 1 аргумент")
    t, v = args[0]
    if t == 'String': print(interpolate_string(v, env))
    else: print(v)
    return ('Void', None)

@krust_builtin("free")
def builtin_free(env, args):
    if len(args) != 1 or args[0][0] != 'String':
        raise RuntimeError("free принимает строку с именем переменной")
    env.free_var(args[0][1])
    return ('Void', None)

@krust_builtin("set")
def builtin_set(env, args):
    if len(args) != 2: raise RuntimeError("set требует 2 аргумента")
    name_t, name = args[0]
    if name_t != 'String': raise RuntimeError("Первый аргумент set должен быть строкой с именем переменной")
    new_value = args[1]
    env.update(name, new_value)
    return ('Void', None)

@krust_builtin("import")
def builtin_import(env, args):
    if len(args) != 1 or args[0][0] != 'String':
        raise RuntimeError("import принимает строку с именем файла")
    filename = args[0][1]
    filepath = os.path.join('libs', f"{filename}.krust")
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            code = f.read()
    except FileNotFoundError:
        raise RuntimeError(f"Библиотека '{filename}.krust' не найдена в папке libs/")
    
    ast = parse(code)
    for node in ast:
        evaluate(node, env, f"импорте '{filename}'")
    return ('Void', None)

@krust_builtin("py_exec")
def builtin_py_exec(env, args):
    if len(args) != 1 or args[0][0] != 'String':
        raise RuntimeError("py_exec принимает одну строку с Python кодом")
    
    raw_code = args[0][1]
    python_code = interpolate_string(raw_code, env)
    
    py_globals = {"__builtins__": __builtins__, "krust_call": krust_invoke_from_python}
    for name, (tp, val) in env.vars.items():
        if tp == 'List': py_globals[name] = [v[1] for v in val if v[0] in ('Int', 'Float', 'String', 'Bool')]
        elif tp == 'Json': py_globals[name] = {k: v[1] for k, v in val.items()}
        else: py_globals[name] = val
            
    try:
        result = eval(python_code, py_globals)
        if isinstance(result, str): return ('String', result)
        if isinstance(result, bool): return ('Bool', result)
        if isinstance(result, int): return ('Int', result)
        if isinstance(result, float): return ('Float', result)
        return ('String', str(result))
    except SyntaxError:
        try:
            exec(python_code, py_globals)
            return ('Void', None)
        except Exception as e:
            raise RuntimeError(f"Python exec error: {e}")
    except Exception as e:
        raise RuntimeError(f"Python eval error: {e}")

# --- Математика ---
@krust_builtin("+")
def builtin_add(env, args):
    if len(args) != 2: raise RuntimeError("+ требует 2 аргумента")
    t1, v1 = args[0]; t2, v2 = args[1]
    if t1 not in ('Int', 'Float') or t2 not in ('Int', 'Float'): raise RuntimeError("+ работает только с числами")
    if t1 == 'Float' or t2 == 'Float': return ('Float', float(v1) + float(v2))
    return ('Int', v1 + v2)

@krust_builtin("-")
def builtin_sub(env, args):
    if len(args) != 2: raise RuntimeError("- требует 2 аргумента")
    t1, v1 = args[0]; t2, v2 = args[1]
    if t1 not in ('Int', 'Float') or t2 not in ('Int', 'Float'): raise RuntimeError("- работает только с числами")
    if t1 == 'Float' or t2 == 'Float': return ('Float', float(v1) - float(v2))
    return ('Int', v1 - v2)

@krust_builtin("*")
def builtin_mul(env, args):
    if len(args) != 2: raise RuntimeError("* требует 2 аргумента")
    t1, v1 = args[0]; t2, v2 = args[1]
    if t1 not in ('Int', 'Float') or t2 not in ('Int', 'Float'): raise RuntimeError("* работает только с числами")
    if t1 == 'Float' or t2 == 'Float': return ('Float', float(v1) * float(v2))
    return ('Int', v1 * v2)

@krust_builtin("/")
def builtin_div(env, args):
    if len(args) != 2: raise RuntimeError("/ требует 2 аргумента")
    t1, v1 = args[0]; t2, v2 = args[1]
    if t1 not in ('Int', 'Float') or t2 not in ('Int', 'Float'): raise RuntimeError("/ работает только с числами")
    if v2 == 0: raise RuntimeError("Деление на ноль")
    if t1 == 'Float' or t2 == 'Float': return ('Float', float(v1) / float(v2))
    return ('Int', v1 // v2)

@krust_builtin("%")
def builtin_mod(env, args):
    if len(args) != 2: raise RuntimeError("% требует 2 аргумента")
    t1, v1 = args[0]; t2, v2 = args[1]
    if t1 != 'Int' or t2 != 'Int': raise RuntimeError("% работает только с Int")
    if v2 == 0: raise RuntimeError("Деление на ноль")
    return ('Int', v1 % v2)

# --- Строки ---
@krust_builtin("str_concat")
def builtin_str_concat(env, args):
    if len(args) < 2: raise RuntimeError("str_concat требует минимум 2 аргумента")
    result = ""
    for arg in args:
        t, v = arg
        if t == 'String': result += v
        elif t in ('Int', 'Float', 'Bool'): result += str(v)
        else: raise RuntimeError(f"str_concat не поддерживает тип {t}")
    return ('String', result)

@krust_builtin("str_split")
def builtin_str_split(env, args):
    if len(args) != 2: raise RuntimeError("str_split требует 2 аргумента (строка, разделитель)")
    string_t, string = args[0]; splitter_t, splitter = args[1] # Исправлен порядок для удобства
    if string_t != 'String': raise RuntimeError("Первый аргумент должен быть String")
    if splitter_t != 'String': raise RuntimeError("Второй аргумент должен быть String")
    return ('List', [('String', part) for part in string.split(splitter)])

@krust_builtin("str_split_max")
def builtin_str_split_max(env, args): # Исправлено имя декоратора
    if len(args) != 3: raise RuntimeError("str_split_max требует 3 аргумента (строка, разделитель, макс)")
    string_t, string = args[0]; splitter_t, splitter = args[1]; max_t, max_val = args[2]
    if string_t != 'String': raise RuntimeError("Первый аргумент должен быть String")
    if splitter_t != 'String': raise RuntimeError("Второй аргумент должен быть String")
    if max_t != 'Int': raise RuntimeError("Третий аргумент должен быть Int") # Исправлено сообщение
    return ('List', [('String', part) for part in string.split(splitter, max_val)])

# --- Списки и Кортежи ---
@krust_builtin("list_push")
def builtin_list_push(env, args):
    if len(args) != 2: raise RuntimeError("list_push требует 2 аргумента")
    t, lst = args[0]
    if t != 'List': raise RuntimeError("Первый аргумент должен быть List")
    lst.append(args[1]); return ('Void', None)

@krust_builtin("list_get")
def builtin_list_get(env, args):
    if len(args) != 2: raise RuntimeError("list_get требует 2 аргумента")
    t, lst = args[0]; idx_t, idx = args[1]
    if t != 'List': raise RuntimeError("Первый аргумент должен быть List")
    if idx_t != 'Int': raise RuntimeError("Индекс должен быть Int")
    if idx < 0 or idx >= len(lst): raise RuntimeError(f"Индекс {idx} вне диапазона")
    return lst[idx]

@krust_builtin("list_length")
def builtin_list_length(env, args):
    if len(args) != 1: raise RuntimeError("list_length требует 1 аргумент")
    t, lst = args[0]
    if t != 'List': raise RuntimeError("Аргумент должен быть List")
    return ('Int', len(lst))

@krust_builtin("in_list")
def builtin_in_list(env, args):
    if len(args) != 2: 
        raise RuntimeError("in_list требует 2 аргумента")

    check_t, check = args[0]
    t, lst = args[1]

    if t != 'List': 
        raise RuntimeError("in_list работает только с типом List")

    return ('Bool', (check_t, check) in lst)
    
@krust_builtin("tuple_get")
def builtin_tuple_get(env, args):
    if len(args) != 2: raise RuntimeError("tuple_get требует 2 аргумента")
    t, tup = args[0]; idx_t, idx = args[1]
    if t != 'Tuple': raise RuntimeError("Первый аргумент должен быть Tuple")
    if idx_t != 'Int': raise RuntimeError("Индекс должен быть Int")
    if idx < 0 or idx >= len(tup): raise RuntimeError(f"Индекс {idx} вне диапазона")
    return tup[idx]

# --- JSON ---
@krust_builtin("json_get")
def builtin_json_get(env, args):
    if len(args) != 2: raise RuntimeError("json_get требует 2 аргумента")
    t, obj = args[0]; key_t, key = args[1]
    if t != 'Json': raise RuntimeError("Первый аргумент должен быть Json")
    if key_t != 'String': raise RuntimeError("Ключ должен быть String")
    if key not in obj: raise RuntimeError(f"Ключ '{key}' не найден")
    return obj[key]

@krust_builtin("json_set")
def builtin_json_set(env, args):
    if len(args) != 3: raise RuntimeError("json_set требует 3 аргумента")
    t, obj = args[0]; key_t, key = args[1]
    if t != 'Json': raise RuntimeError("Первый аргумент должен быть Json")
    if key_t != 'String': raise RuntimeError("Ключ должен быть String")
    obj[key] = args[2]; return ('Void', None)

@krust_builtin("json_to_string")
def builtin_json_to_string(env, args):
    if len(args) != 1: raise RuntimeError("json_to_string требует 1 аргумент")
    t, obj = args[0]
    if t != 'Json': raise RuntimeError("Аргумент должен быть Json")
    def convert(val):
        tp, v = val
        if tp in ('String', 'Int', 'Float', 'Bool'): return v
        if tp == 'List': return [convert(x) for x in v]
        if tp == 'Json': return {k: convert(vv) for k, vv in v.items()}
        return None
    return ('String', json_module.dumps(convert(obj)))

# --- Системные ---
@krust_builtin("ffi_exec")
def builtin_ffi_exec(env, args):
    if len(args) != 3: raise RuntimeError("ffi_exec требует 3 аргумента")
    path_t, path = args[0]; func_t, func_name = args[1]; params_t, params = args[2]
    if path_t != 'String': raise RuntimeError("Путь должен быть String")
    if func_t != 'String': raise RuntimeError("Имя функции должно быть String")
    if params_t != 'List': raise RuntimeError("Параметры должны быть List")
    try:
        lib = ctypes.CDLL(path)
        func = getattr(lib, func_name)
        c_args = []
        for param in params:
            tp, val = param
            if tp == 'Int': c_args.append(ctypes.c_int(val))
            elif tp == 'Float': c_args.append(ctypes.c_double(val))
            elif tp == 'String': c_args.append(ctypes.c_char_p(val.encode('utf-8')))
            elif tp == 'Bool': c_args.append(ctypes.c_int(1 if val else 0))
            else: raise RuntimeError(f"Неподдерживаемый тип FFI: {tp}")
        return ('Int', func(*c_args))
    except Exception as e:
        raise RuntimeError(f"FFI ошибка: {e}")

@krust_builtin("input")
def builtin_input(env, args):
    if len(args) != 1: raise RuntimeError("input требует 1 аргумента")
    prompt_t, prompt = args[0]
    if prompt_t != 'String': raise RuntimeError("Prompt должен быть String")
    return ('String', input(prompt))

@krust_builtin("sleep")
def builtin_sleep(env, args):
    if len(args) != 1: raise RuntimeError("sleep требует 1 аргумент (секунды)")
    t, v = args[0]
    if t not in ('Int', 'Float'): raise RuntimeError("sleep требует число")
    time.sleep(float(v))
    return ('Void', None)

@krust_builtin("thread")
def builtin_thread(env, args):
    if len(args) < 1:
        raise RuntimeError("thread требует минимум 1 аргумент (имя функции)")
    func_name_t, func_name = args[0]
    if func_name_t != 'String':
        raise RuntimeError("Первый аргумент thread должен быть строкой")
    py_args = [arg[1] for arg in args[1:]]
    
    def thread_target():
        try:
            krust_invoke_from_python(func_name, *py_args)
        except Exception as e:
            print(f"[THREAD ERROR in '{func_name}'] {e}")

    t = threading.Thread(target=thread_target, daemon=True)
    t.start()
    return ('Void', None)

@krust_builtin("hash")
def builtin_hash(env, args):
    if len(args) < 2: raise RuntimeError("hash требует 2 аргумента (тип, данные)")
    hash_t, hash_type = args[0]; data_t, data = args[1]
    if hash_t != 'String': raise RuntimeError("Тип хеширования должен быть String")
    _hash = hashlib.new(hash_type, data.encode()).hexdigest()
    return ('String', _hash)

@krust_builtin("file_write")
def builtin_file_write(env, args):
    if len(args) < 2: raise RuntimeError("file_write требует 2 аргумента (файл, данные)")
    file_t, file = args[0]; data_t, data = args[1]
    if file_t != 'String': raise RuntimeError("Имя файла должно быть String")
    with open(file, 'w', encoding='utf-8') as f:
        f.write(data)
    return ('Void', None)

@krust_builtin("file_read")
def builtin_file_read(env, args):
    if len(args) < 1: raise RuntimeError("file_read требует 1 аргумент (файл)") # Исправлено сообщение
    file_t, file = args[0]
    if file_t != 'String': raise RuntimeError("Имя файла должно быть String")
    with open(file, 'r', encoding='utf-8') as f:
        data = f.read()
    return ('String', data)

@krust_builtin("exec_krust_func")
def builtin_exec_krust_func(env, args):
    if len(args) < 1:
        raise RuntimeError("exec_krust_func требует минимум 1 аргумент (имя функции)")
    func_t, func = args[0]
    if func_t != 'String':
        raise RuntimeError("Имя функции должно быть String")
    py_args = [arg[1] for arg in args[1:]]
    result = krust_invoke_from_python(func, *py_args)
    
    if result is None: return ('Void', None)
    elif isinstance(result, str): return ('String', result)
    elif isinstance(result, bool): return ('Bool', result)
    elif isinstance(result, int): return ('Int', result)
    elif isinstance(result, float): return ('Float', result)
    elif isinstance(result, list): return ('List', result)
    else: return ('String', str(result))

# --- Конвертация типов ---
@krust_builtin("to_string")
def builtin_to_string(env, args):
    if len(args) != 1: raise RuntimeError("to_string требует 1 аргумент")
    t, v = args[0]
    if t == 'String': return ('String', v)
    elif t in ('Int', 'Float'): return ('String', str(v))
    elif t == 'Bool': return ('String', 'true' if v else 'false')
    elif t == 'List':
        items = [builtin_to_string(env, [item])[1] for item in v]
        return ('String', '[' + ', '.join(items) + ']')
    elif t == 'Tuple':
        items = [builtin_to_string(env, [item])[1] for item in v]
        return ('String', '(' + ', '.join(items) + ')')
    elif t == 'Json': return builtin_json_to_string(env, args)
    elif t == 'Void': return ('String', 'void')
    else: raise RuntimeError(f"to_string не поддерживает тип {t}")

@krust_builtin("to_int")
def builtin_to_int(env, args):
    if len(args) != 1: raise RuntimeError("to_int требует 1 аргумент")
    t, v = args[0]
    if t == 'Int': return ('Int', v)
    elif t == 'Float': return ('Int', int(v))
    elif t == 'Bool': return ('Int', 1 if v else 0)
    elif t == 'String':
        try:
            return ('Int', int(float(v)) if '.' in v else int(v))
        except ValueError:
            raise RuntimeError(f"Невозможно конвертировать строку '{v}' в Int")
    else: raise RuntimeError(f"to_int не поддерживает тип {t}")

@krust_builtin("to_float")
def builtin_to_float(env, args):
    if len(args) != 1: raise RuntimeError("to_float требует 1 аргумент")
    t, v = args[0]
    if t == 'Float': return ('Float', v)
    elif t == 'Int': return ('Float', float(v))
    elif t == 'Bool': return ('Float', 1.0 if v else 0.0)
    elif t == 'String':
        try: return ('Float', float(v))
        except ValueError: raise RuntimeError(f"Невозможно конвертировать строку '{v}' в Float")
    else: raise RuntimeError(f"to_float не поддерживает тип {t}")

@krust_builtin("to_bool")
def builtin_to_bool(env, args):
    if len(args) != 1: raise RuntimeError("to_bool требует 1 аргумент")
    t, v = args[0]
    if t == 'Bool': return ('Bool', v)
    elif t in ('Int', 'Float'): return ('Bool', v != 0)
    elif t == 'String':
        lower = v.lower().strip()
        if lower in ('true', '1', 'yes', 'on'): return ('Bool', True)
        elif lower in ('false', '0', 'no', 'off', ''): return ('Bool', False)
        else: raise RuntimeError(f"Невозможно конвертировать строку '{v}' в Bool")
    elif t == 'List': return ('Bool', len(v) > 0)
    elif t == 'Void': return ('Bool', False)
    else: raise RuntimeError(f"to_bool не поддерживает тип {t}")

@krust_builtin("to_list")
def builtin_to_list(env, args):
    if len(args) != 1: raise RuntimeError("to_list требует 1 аргумент")
    t, v = args[0]
    if t == 'List': return ('List', v)
    elif t == 'Tuple': return ('List', list(v))
    elif t == 'String': return ('List', [('String', char) for char in v])
    elif t == 'Json':
        if isinstance(v, list): return ('List', v)
        return ('List', [('String', key) for key in v.keys()])
    else: raise RuntimeError(f"to_list не поддерживает тип {t}")

@krust_builtin("to_json")
def builtin_to_json(env, args):
    if len(args) != 1: raise RuntimeError("to_json требует 1 аргумент")
    t, v = args[0]
    if t == 'Json': return ('Json', v)
    elif t == 'String':
        try:
            parsed = json_module.loads(v)
            def convert(val):
                if isinstance(val, str): return ('String', val)
                elif isinstance(val, bool): return ('Bool', val)
                elif isinstance(val, int): return ('Int', val)
                elif isinstance(val, float): return ('Float', val)
                elif isinstance(val, list): return ('List', [convert(item) for item in val])
                elif isinstance(val, dict): return ('Json', {k: convert(vv) for k, vv in val.items()})
                elif val is None: return ('Void', None)
                else: return ('String', str(val))
            return convert(parsed)
        except json_module.JSONDecodeError as e:
            raise RuntimeError(f"Невалидный JSON: {e}")
    else: raise RuntimeError(f"to_json не поддерживает тип {t}")

@krust_builtin("type_of")
def builtin_type_of(env, args):
    if len(args) != 1: raise RuntimeError("type_of требует 1 аргумент")
    t, v = args[0]
    return ('String', t)

# --- Сравнение ---
@krust_builtin("==")
def builtin_eq(env, args):
    if len(args) != 2: raise RuntimeError("== требует 2 аргумента")
    t1, v1 = args[0]; t2, v2 = args[1]
    if t1 != t2: return ('Bool', False)
    return ('Bool', v1 == v2)

@krust_builtin("!=")
def builtin_neq(env, args):
    if len(args) != 2: raise RuntimeError("!= требует 2 аргумента")
    t1, v1 = args[0]; t2, v2 = args[1]
    if t1 != t2: return ('Bool', True)
    return ('Bool', v1 != v2)

@krust_builtin(">")
def builtin_gt(env, args):
    if len(args) != 2: raise RuntimeError("> требует 2 аргумента")
    t1, v1 = args[0]; t2, v2 = args[1]
    if t1 not in ('Int', 'Float') or t2 not in ('Int', 'Float'): raise RuntimeError("> только для чисел")
    return ('Bool', float(v1) > float(v2))

@krust_builtin("<")
def builtin_lt(env, args):
    if len(args) != 2: raise RuntimeError("< требует 2 аргумента")
    t1, v1 = args[0]; t2, v2 = args[1]
    if t1 not in ('Int', 'Float') or t2 not in ('Int', 'Float'): raise RuntimeError("< только для чисел")
    return ('Bool', float(v1) < float(v2))

@krust_builtin(">=")
def builtin_gte(env, args):
    if len(args) != 2: raise RuntimeError(">= требует 2 аргумента")
    t1, v1 = args[0]; t2, v2 = args[1]
    if t1 not in ('Int', 'Float') or t2 not in ('Int', 'Float'): raise RuntimeError(">= только для чисел")
    return ('Bool', float(v1) >= float(v2))

@krust_builtin("<=")
def builtin_lte(env, args):
    if len(args) != 2: raise RuntimeError("<= требует 2 аргумента")
    t1, v1 = args[0]; t2, v2 = args[1]
    if t1 not in ('Int', 'Float') or t2 not in ('Int', 'Float'): raise RuntimeError("<= только для чисел")
    return ('Bool', float(v1) <= float(v2))

# --- Ссылки ---
@krust_builtin("ref")
def builtin_ref(env, args):
    """Возвращает ссылку на переменную: (ref, "var_name")"""
    if len(args) != 1 or args[0][0] != 'String':
        raise RuntimeError("ref требует 1 аргумент: имя переменной (строку)")
    
    var_name = args[0][1]
    # Проверяем, существует ли переменная, прежде чем брать на неё ссылку
    try:
        env.get(var_name)
    except RuntimeError:
        raise RuntimeError(f"Невозможно взять ссылку: переменная '{var_name}' не найдена")
    
    return ('Ref', var_name)

@krust_builtin("deref")
def builtin_deref(env, args):
    """Разыменовывает ссылку и возвращает значение: (deref, my_ref)"""
    if len(args) != 1 or args[0][0] != 'Ref':
        raise RuntimeError("deref требует 1 аргумент: ссылку (Ref)")
    
    var_name = args[0][1]

    return env.get(var_name)

@krust_builtin("set_ref")
def builtin_set_ref(env, args):
    """Изменяет значение переменной через ссылку: (set_ref, my_ref, new_value)"""
    if len(args) != 2 or args[0][0] != 'Ref':
        raise RuntimeError("set_ref требует 2 аргумента: (ссылка, новое_значение)")
    
    var_name = args[0][1]
    new_value = args[1]
    
    env.update(var_name, new_value)
    return ('Void', None)

# --- Запросы ---
@krust_builtin("request")
def builtin_request(env, args):
    """
    Выполняет HTTP-запрос.
    
    Аргументы:
    1. URL (String) - адрес запроса
    2. Метод (String) - 'GET', 'POST', 'PUT', 'DELETE', 'PATCH', 'HEAD'
    3. Данные (Json/List/Void) - тело запроса (для POST/PUT/PATCH)
    4. Заголовки (Json/Void) - дополнительные заголовки (опционально)
    
    Возвращает Json с полями:
    - status: Int - код ответа
    - headers: Json - заголовки ответа
    - body: String/Json - тело ответа (автоматически парсится JSON)
    - error: String - сообщение об ошибке (если есть)
    """
    
    # Проверяем минимальное количество аргументов
    if len(args) < 2:
        raise RuntimeError("request требует минимум 2 аргумента: (url, method)")
    
    # Парсим URL
    url_t, url = args[0]
    if url_t != 'String':
        raise RuntimeError("Первый аргумент должен быть String (URL)")
    
    # Парсим метод
    method_t, method = args[1]
    if method_t != 'String':
        raise RuntimeError("Второй аргумент должен быть String (метод)")
    
    method = method.upper()
    valid_methods = {'GET', 'POST', 'PUT', 'DELETE', 'PATCH', 'HEAD'}
    if method not in valid_methods:
        raise RuntimeError(f"Неверный метод: {method}. Допустимые: {', '.join(valid_methods)}")
    
    # Парсим данные (опционально)
    data = None
    json_data = None
    if len(args) > 2:
        data_t, data_val = args[2]
        if data_t == 'Json':
            # Преобразуем Json в Python dict
            json_data = convert_krust_json_to_python(data_val)
        elif data_t == 'List':
            # Преобразуем List в Python list
            json_data = convert_krust_list_to_python(data_val)
        elif data_t == 'String':
            data = data_val
        elif data_t in ('Int', 'Float', 'Bool'):
            data = str(data_val)
        elif data_t != 'Void':
            raise RuntimeError(f"Неподдерживаемый тип данных: {data_t}")
    
    # Парсим заголовки (опционально)
    headers = {}
    if len(args) > 3:
        headers_t, headers_val = args[3]
        if headers_t == 'Json':
            headers = convert_krust_json_to_python(headers_val)
        elif headers_t != 'Void':
            raise RuntimeError("Заголовки должны быть Json или Void")
    
    # Добавляем Content-Type для JSON данных
    if json_data is not None and 'Content-Type' not in headers:
        headers['Content-Type'] = 'application/json'
    
    try:
        # Выполняем запрос
        response = None
        
        if method == 'GET':
            response = requests.get(url, headers=headers, timeout=30)
        elif method == 'POST':
            if json_data is not None:
                response = requests.post(url, json=json_data, headers=headers, timeout=30)
            else:
                response = requests.post(url, data=data, headers=headers, timeout=30)
        elif method == 'PUT':
            if json_data is not None:
                response = requests.put(url, json=json_data, headers=headers, timeout=30)
            else:
                response = requests.put(url, data=data, headers=headers, timeout=30)
        elif method == 'DELETE':
            if json_data is not None:
                response = requests.delete(url, json=json_data, headers=headers, timeout=30)
            else:
                response = requests.delete(url, data=data, headers=headers, timeout=30)
        elif method == 'PATCH':
            if json_data is not None:
                response = requests.patch(url, json=json_data, headers=headers, timeout=30)
            else:
                response = requests.patch(url, data=data, headers=headers, timeout=30)
        elif method == 'HEAD':
            response = requests.head(url, headers=headers, timeout=30)
        
        # Парсим тело ответа
        body = None
        content_type = response.headers.get('Content-Type', '').lower()
        
        # Пытаемся парсить JSON
        if 'application/json' in content_type:
            try:
                body = response.json()
                body_krust = convert_python_to_krust(body)
            except:
                body_krust = ('String', response.text)
        else:
            body_krust = ('String', response.text)
        
        # Формируем результат
        result_headers = {}
        for key, value in response.headers.items():
            if isinstance(value, str):
                result_headers[key] = ('String', value)
            else:
                result_headers[key] = ('String', str(value))
        
        result = {
            'status': ('Int', response.status_code),
            'headers': ('Json', result_headers),
            'body': body_krust,
            'error': ('Void', None)
        }
        
        return ('Json', result)
        
    except requests.exceptions.Timeout:
        return ('Json', {
            'status': ('Int', 0),
            'headers': ('Json', {}),
            'body': ('String', ''),
            'error': ('String', 'Timeout')
        })
    except requests.exceptions.ConnectionError:
        return ('Json', {
            'status': ('Int', 0),
            'headers': ('Json', {}),
            'body': ('String', ''),
            'error': ('String', 'Connection Error')
        })
    except requests.exceptions.RequestException as e:
        return ('Json', {
            'status': ('Int', 0),
            'headers': ('Json', {}),
            'body': ('String', ''),
            'error': ('String', str(e))
        })
    except Exception as e:
        raise RuntimeError(f"Ошибка при выполнении запроса: {e}")

# Вспомогательные функции для конвертации между Krust и Python
def convert_krust_json_to_python(krust_json):
    """Конвертирует Krust Json в Python dict"""
    result = {}
    for key, value in krust_json.items():
        result[key] = convert_krust_value_to_python(value)
    return result

def convert_krust_list_to_python(krust_list):
    """Конвертирует Krust List в Python list"""
    result = []
    for item in krust_list:
        result.append(convert_krust_value_to_python(item))
    return result

def convert_krust_value_to_python(krust_value):
    """Конвертирует любое Krust значение в Python"""
    if not isinstance(krust_value, tuple) and not isinstance(krust_value, list):
        return krust_value
    
    tp, val = krust_value
    if tp == 'String':
        return val
    elif tp == 'Int':
        return val
    elif tp == 'Float':
        return val
    elif tp == 'Bool':
        return val
    elif tp == 'List':
        return convert_krust_list_to_python(val)
    elif tp == 'Json':
        return convert_krust_json_to_python(val)
    elif tp == 'Void':
        return None
    else:
        return val

def convert_python_to_krust(py_value):
    """Конвертирует Python значение в Krust"""
    if py_value is None:
        return ('Void', None)
    elif isinstance(py_value, str):
        return ('String', py_value)
    elif isinstance(py_value, bool):
        return ('Bool', py_value)
    elif isinstance(py_value, int):
        return ('Int', py_value)
    elif isinstance(py_value, float):
        return ('Float', py_value)
    elif isinstance(py_value, list):
        return ('List', [convert_python_to_krust(item) for item in py_value])
    elif isinstance(py_value, dict):
        result = {}
        for key, value in py_value.items():
            result[key] = convert_python_to_krust(value)
        return ('Json', result)
    else:
        return ('String', str(py_value))

# --- Системные функции ---
@krust_builtin("system_info")
def builtin_system_info(env, args):
    return ('Json', {
        "system": os.name,
        "system_ver": platform.version(),
        "krust_version": VERSION
    })

# ==========================================
# 5. Интерпретатор с Traceback
# ==========================================
def evaluate(node, env, current_frame="<main>"):
    try:
        if node[0] == 'StringLit': return ('String', node[1])
        if node[0] == 'IntLit': return ('Int', node[1])
        if node[0] == 'FloatLit': return ('Float', node[1])
        if node[0] == 'BoolLit': return ('Bool', node[1])
        
        if node[0] == 'ListLit': return ('List', [evaluate(item, env, current_frame) for item in node[1]])
        if node[0] == 'TupleLit': return ('Tuple', [evaluate(item, env, current_frame) for item in node[1]])
        if node[0] == 'JsonLit': return ('Json', {key: evaluate(val_node, env, current_frame) for key, val_node in node[1]})
        if node[0] == 'Ident': return env.get(node[1])

        if node[0] == 'VarDecl':
            _, type_name, var_name, value_node = node
            val_type, val = evaluate(value_node, env, current_frame)
            if val_type != type_name:
                raise RuntimeError(f"Ошибка типизации: ожидался {type_name}, получено {val_type}")
            env.set(var_name, (val_type, val))
            env.memory.alloc(var_name)
            return ('Void', None)

        if node[0] == 'FuncDef':
            _, name, params, body = node
            env.set_func(name, (params, body, env))
            return ('Void', None)

        if node[0] == 'Block':
            _, stmts = node
            res = ('Void', None)
            for stmt in stmts:
                res = evaluate(stmt, env, current_frame)
            return res

        if node[0] == 'Return':
            _, value_node = node
            raise ReturnException(evaluate(value_node, env, current_frame))

        if node[0] == 'If':
            _, cond_node, true_block = node
            cond_type, cond_val = evaluate(cond_node, env, current_frame)
            if cond_type == 'Bool' and cond_val == True:
                return evaluate(true_block, env, current_frame)
            return ('Void', None)

        if node[0] == 'For':
            _, var_name, iterable_node, body = node
            iter_type, iter_val = evaluate(iterable_node, env, current_frame)
            if iter_type not in ('List', 'Tuple'):
                raise RuntimeError(f"for работает только с List или Tuple, получен {iter_type}")
            
            result = ('Void', None)
            for item in iter_val:
                loop_env = Environment(env)
                loop_env.set(var_name, item)
                loop_env.memory.alloc(var_name)
                try:
                    result = evaluate(body, loop_env, current_frame)
                except BreakException:
                    break
                except ContinueException:
                    continue
                finally:
                    if var_name in loop_env.vars:
                        loop_env.free_var(var_name)
            return result

        if node[0] == 'While':
            _, cond_node, body = node
            result = ('Void', None)
            while True:
                cond_type, cond_val = evaluate(cond_node, env, current_frame)
                if cond_type != 'Bool':
                    raise RuntimeError("Условие while должно быть Bool")
                if not cond_val:
                    break
                try:
                    result = evaluate(body, env, current_frame)
                except BreakException:
                    break
                except ContinueException:
                    continue
            return result

        if node[0] == 'FuncCall':
            _, name, args = node
            if name in BUILTINS:
                return BUILTINS[name](env, [evaluate(arg, env, current_frame) for arg in args])

            func_data = env.get_func(name)
            if not func_data:
                raise RuntimeError(f"Функция '{name}' не определена")
                
            params, body, closure_env = func_data
            if len(params) != len(args):
                raise RuntimeError(f"Функция '{name}' ожидает {len(params)} аргументов, передано {len(args)}")

            new_env = Environment(closure_env)
            evaluated_args = []
            for a in args:
                evaluated_args.append(evaluate(a, env, current_frame))
            
            for p, val in zip(params, evaluated_args):
                new_env.set(p, val)

            try:
                # Добавляем имя функции в стек вызовов при рекурсивном вызове
                return evaluate(body, new_env, f"функции '{name}'")
            except ReturnException as e:
                return e.value
            except KrustError as de:
                # Пробрасываем KrustError наверх, добавляя текущий фрейм
                de.add_frame(f"функции '{name}'")
                raise

        raise RuntimeError(f"Неизвестный узел AST: {node}")
        
    except KrustError:
        # Если это уже наша ошибка с трейсбеком, просто пробрасываем её дальше
        raise
    except Exception as e:
        # Оборачиваем любые другие ошибки Python в KrustError с указанием места
        raise KrustError(str(e), current_frame)

# ==========================================
# 6. Точка входа
# ==========================================
def run_krust(code):
    global GLOBAL_KRUST_ENV

    env = Environment()
    GLOBAL_KRUST_ENV = env
    try:
        ast = parse(code)
        for node in ast:
            evaluate(node, env, "<main>")
    except KrustError as e:
        print(e)
    except Exception as e:
        print(f"[KRUST ERROR] Неожиданная ошибка Python: {e}")

if __name__ == "__main__":
    argparser = argparse.ArgumentParser('Krust Language', description='A Functional Programming Language')

    argparser.add_argument('file', help='Файл для исполнения')

    args = argparser.parse_args()

    with open(args.file, 'r') as f:
        krust_code = f.read()

    start = time.time()

    run_krust(krust_code)

    end = time.time()
    print(f"\nВсего выполнено за {end - start:.4f} сек.")