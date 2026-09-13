import gc
import re
import sys
import os
import ctypes
from ctypes import CFUNCTYPE, c_int, c_char_p, c_void_p, c_double, Structure, POINTER
import json as json_module
import time
import threading
import hashlib
import argparse
import platform
import requests
import urllib.parse

VERSION = 'b1.0'

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
    lines = code.split('\n')
    # Создаем карту позиций для быстрого поиска строки по индексу
    line_starts = [0]
    for line in lines:
        line_starts.append(line_starts[-1] + len(line) + 1)

    def get_pos(index):
        # Бинарный поиск или простой проход для определения строки
        line_num = 1
        for i, start in enumerate(line_starts):
            if index < start:
                break
            line_num = i + 1
        col = index - line_starts[line_num - 1] + 1
        return line_num, col

    for mo in re.finditer(TOKEN_REGEX, code):
        kind = mo.lastgroup
        value = mo.group()
        start_idx = mo.start()
        line, col = get_pos(start_idx)
        
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
            tokens.append(('IDENT', OPERATOR_MAP[kind], line, col))
            continue
        elif kind == 'MISMATCH':
            raise RuntimeError(f'Недопустимый символ: {value} в строке {line}:{col}')
        
        tokens.append((kind, value, line, col))
    
    tokens.append(('EOF', None, len(lines), 1))
    return tokens

# ==========================================
# 2. Парсер
# ==========================================
VALID_TYPES = {'String', 'Int', 'Float', 'Bool', 'Void', 'Tuple', 'List', 'Json', 'Ref', 'Func'}

def peek(tokens, offset=0):
    if offset < len(tokens): return tokens[offset]
    return ('EOF', None)

def expect(tokens, kind):
    if not tokens:
        raise SyntaxError(f"Неожиданный конец файла. Ожидалось: {kind}")
    
    if tokens[0][0] != kind:
        got_type, got_val, line, col = tokens[0]
        raise SyntaxError(f"Ошибка синтаксиса в строке {line}:{col}. Ожидалось {kind}, получено {got_type} ('{got_val}')")
    
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
    if not tokens: raise SyntaxError("Unexpected end of input")
    first = tokens[0]
    
    if first[0] == 'LPAREN':
        second = peek(tokens, 1)
        if second and second[0] == 'IDENT':
            val = second[1]
            if val == 'func': return parse_func_def(tokens)
            if val in VALID_TYPES: return parse_var_decl(tokens)
            if val == 'return': return parse_return(tokens)
            if val == 'if': return parse_if(tokens)
            if val == 'for': return parse_for(tokens)
            if val == 'while': return parse_while(tokens)
            return parse_func_call(tokens)
        
        if second and second[0] in ('NUMBER', 'STRING', 'BOOL', 'LBRACKET', 'LBRACE', 'LPAREN'): 
            return parse_tuple(tokens)
            
        raise SyntaxError(f"Неизвестная конструкция после (: second={second}")
    
    return parse_primary(tokens)

def parse_func_def(tokens):
    expect(tokens, 'LPAREN'); expect(tokens, 'IDENT')
    name = expect(tokens, 'IDENT')[1]; expect(tokens, 'COMMA')
    expect(tokens, 'LPAREN')  # (
    params = []
    while tokens[0][0] != 'RPAREN':
        params.append(expect(tokens, 'IDENT')[1])
        if tokens[0][0] == 'COMMA': tokens.pop(0)
    expect(tokens, 'RPAREN'); expect(tokens, 'ARROW')
    
    body = parse_expr(tokens)
    
    expect(tokens, 'RPAREN')
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
    
    # Если сразу закрывающая скобка - выходим
    if tokens[0][0] == 'RPAREN':
        expect(tokens, 'RPAREN')
        return ('FuncCall', func_name, args)

    while tokens[0][0] != 'RPAREN':
        expect(tokens, 'COMMA')
        
        # Если после запятой сразу идет закрывающая скобка (висячая запятая), игнорируем её
        if tokens[0][0] == 'RPAREN':
            break
            
        args.append(parse_expr(tokens))
        
    expect(tokens, 'RPAREN')
    return ('FuncCall', func_name, args)

def parse_tuple(tokens):
    expect(tokens, 'LPAREN')
    items = []
    if tokens[0][0] != 'RPAREN':
        items.append(parse_expr(tokens))
        while tokens[0][0] == 'COMMA':
            tokens.pop(0)
            if tokens[0][0] == 'RPAREN': break # Висячая запятая
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
        try:
            _, val = env.get(var_name)
            return str(val)
        except:
            return match.group(0)
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

    # Ищем библиотеку относительно директории интерпретатора
    base_dir = os.path.dirname(os.path.abspath(__file__))
    filepath = os.path.join(base_dir, 'libs', f"{filename}.kr")

    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            code = f.read()
    except FileNotFoundError:
        raise RuntimeError(f"Библиотека '{filename}.kr' не найдена в {os.path.join(base_dir, 'libs')}")

    ast = parse(code)

    # Создаём ИЗОЛИРОВАННОЕ окружение для библиотеки
    lib_env = Environment(env)  # parent = env, чтобы видеть внешние переменные

    # Локальные __FILENAME__ / __DIRNAME__ — свои у каждой библиотеки
    lib_filename = os.path.basename(filepath)
    lib_dirname  = os.path.dirname(filepath)
    lib_env.set('__FILENAME__', ('String', lib_filename))
    lib_env.set('__DIRNAME__',  ('String', lib_dirname))
    lib_env.set('__LIBNAME__',  ('String', filename))  # на всякий случай

    for node in ast:
        evaluate(node, lib_env, f"импорте '{filename}'")

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
    string_t, string = args[0]; splitter_t, splitter = args[1]
    if string_t != 'String': raise RuntimeError("Первый аргумент должен быть String")
    if splitter_t != 'String': raise RuntimeError("Второй аргумент должен быть String")
    return ('List', [('String', part) for part in string.split(splitter)])

@krust_builtin("str_split_max")
def builtin_str_split_max(env, args):
    if len(args) != 3: raise RuntimeError("str_split_max требует 3 аргумента (строка, разделитель, макс)")
    string_t, string = args[0]; splitter_t, splitter = args[1]; max_t, max_val = args[2]
    if string_t != 'String': raise RuntimeError("Первый аргумент должен быть String")
    if splitter_t != 'String': raise RuntimeError("Второй аргумент должен быть String")
    if max_t != 'Int': raise RuntimeError("Третий аргумент должен быть Int")
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

# --- Функции высшего порядка (Коллбэки в Krust) ---

def call_krust_value(func_node, args_vals, env):
    """Универсальный вызов значения, которое может быть функцией или ссылкой на неё"""
    t, v = func_node
    
    # Если это идентификатор, resolvим его
    if t == 'Ident':
        try:
            resolved = env.get(v)
            return call_krust_value(resolved, args_vals, env)
        except RuntimeError:
            func_data = env.get_func(v)
            if func_data:
                return call_krust_value(('FuncRef', func_data), args_vals, env)
            raise RuntimeError(f"'{v}' не найдено")
            
    # Если это ссылка на функцию (FuncRef)
    if t == 'FuncRef':
        params, body, closure_env = v
        if len(params) != len(args_vals):
            raise RuntimeError(f"Функция ожидает {len(params)} аргументов, передано {len(args_vals)}")
        
        new_env = Environment(closure_env)
        for p, val in zip(params, args_vals):
            new_env.set(p, val)
            
        try:
            # evaluate возвращает результат последнего выражения в блоке
            res = evaluate(body, new_env, "<callback>")
            return res
        except ReturnException as e:
            # Если был return, берем его значение
            return e.value
        except KrustError:
            raise
        except Exception as ex:
            raise KrustError(str(ex), "<callback>")
    else:
        raise RuntimeError(f"Объект типа {t} не является вызываемым")

@krust_builtin("map")
def builtin_map(env, args):
    if len(args) != 2: raise RuntimeError("map требует 2 аргумента")
    func_arg = args[0]
    list_arg = args[1]
    if list_arg[0] != 'List': raise RuntimeError("Второй аргумент map должен быть List")
    
    lst = list_arg[1]
    result = []
    print(f"MAP: {lst}")
    for item in lst:
        # item - это уже кортеж (type, val), например ('Int', 1)
        res = call_krust_value(func_arg, [item], env)
        # res - это тоже кортеж (type, val), например ('Int', 2)
        print(item + ":")

        result.append(res)
        
    return ('List', result)

@krust_builtin("filter")
def builtin_filter(env, args):
    """ filter(func, list) -> возвращает список элементов, где func вернул true """
    if len(args) != 2: raise RuntimeError("filter требует 2 аргумента: (func, list)")
    func_arg = args[0]
    list_arg = args[1]
    if list_arg[0] != 'List': raise RuntimeError("Второй аргумент filter должен быть List")
    
    lst = list_arg[1]
    result = []
    for item in lst:
        res = call_krust_value(func_arg, [item], env)
        if res[0] == 'Bool' and res[1] == True:
            result.append(item)
    return ('List', result)

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

# --- FFI и Коллбэки (C <-> Krust) ---

_active_ffi_callbacks = {}

KRUST_TO_C_TYPE = {
    'Int': c_int,
    'Float': c_double,
    'String': c_char_p,
    'Bool': c_int,
    'Void': None
}

@krust_builtin("ffi_exec")
def builtin_ffi_exec(env, args):
    """
    ffi_exec(path, func_name, arg_types_list, return_type, args_values_list)
    Поддерживает передачу функций Krust как коллбэков (тип аргумента 'Func').
    """
    if len(args) != 5:
        raise RuntimeError("ffi_exec требует 5 аргументов")
        
    path_t, path = args[0]
    func_name_t, func_name = args[1]
    arg_types_t, arg_types_list = args[2] # List of ('String', 'Int')...
    ret_type_t, ret_type = args[3]
    values_t, values_list = args[4] # List of actual values
    
    if path_t != 'String' or func_name_t != 'String':
        raise RuntimeError("Путь и имя функции должны быть строками")
    if arg_types_t != 'List' or values_t != 'List':
        raise RuntimeError("Типы и значения должны быть списками")
    if len(arg_types_list) != len(values_list):
        raise RuntimeError("Несовпадение количества типов и значений")
        
    try:
        lib = ctypes.CDLL(path)
        func = getattr(lib, func_name)
        
        c_arg_types = []
        c_args = []
        
        for i, type_node in enumerate(arg_types_list):
            t, type_name = type_node
            val_node = values_list[i]
            v_t, v_val = val_node
            
            # Обработка коллбэков (передача функции Krust в C)
            if type_name == 'Func':
                # Создаем C-совместимую обертку. 
                # ВАЖНО: Для простоты здесь реализован коллбэк сигнатуры int -> int.
                # В продакшене нужно парсить сигнатуру коллбэка отдельно.
                CB_TYPE = CFUNCTYPE(c_int, c_int)
                
                def make_cb_wrapper(krust_func_node):
                    def c_callback(c_arg):
                        try:
                            res = call_krust_value(krust_func_node, [('Int', c_arg)], env)
                            if res[0] == 'Int': return res[1]
                            return 0
                        except Exception as e:
                            print(f"[FFI CB Error]: {e}")
                            return 0
                    return c_callback
                
                wrapper = make_cb_wrapper(val_node)
                c_cb = CB_TYPE(wrapper)
                _active_ffi_callbacks[id(c_cb)] = c_cb # Сохраняем от GC
                
                c_arg_types.append(CB_TYPE)
                c_args.append(c_cb)
                
            else:
                c_type = KRUST_TO_C_TYPE.get(type_name)
                if c_type is None: raise RuntimeError(f"Неизвестный тип FFI: {type_name}")
                c_arg_types.append(c_type)
                
                if type_name == 'Int': c_args.append(c_int(v_val))
                elif type_name == 'Float': c_args.append(c_double(v_val))
                elif type_name == 'String': c_args.append(c_char_p(v_val.encode('utf-8')))
                elif type_name == 'Bool': c_args.append(c_int(1 if v_val else 0))
                
        func.argtypes = c_arg_types
        
        # Return type handling
        if ret_type == 'Void':
            func.restype = None
            func(*c_args)
            return ('Void', None)
        elif ret_type == 'Int':
            func.restype = c_int
            return ('Int', func(*c_args))
        elif ret_type == 'Float':
            func.restype = c_double
            return ('Float', func(*c_args))
        elif ret_type == 'String':
            func.restype = c_char_p
            res = func(*c_args)
            return ('String', res.decode('utf-8') if res else "")
        elif ret_type == 'Bool':
            func.restype = c_int
            return ('Bool', bool(func(*c_args)))
        else:
            raise RuntimeError(f"Неподдерживаемый тип возврата: {ret_type}")
            
    except Exception as e:
        raise RuntimeError(f"FFI ошибка: {e}")

# --- Системные ---
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
    if len(args) < 1: raise RuntimeError("file_read требует 1 аргумент (файл)")
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

@krust_builtin("raise")
def builtin_raise(env, args):
    if len(args) != 1:
        raise RuntimeError("raise требует 1 аргумент (ошибка)")

    error_t, error = args[0]

    if error_t != 'String':
        raise RuntimeError("Имя ошибки должно быть String")

    raise KrustError(error, "<raise>")

# --- Конвертация типов ---
@krust_builtin("to_string")
def builtin_to_string(env, args):
    if len(args) != 1: raise RuntimeError("to_string требует 1 аргумент")
    t, v = args[0]
    
    if t == 'String': return ('String', v)
    elif t in ('Int', 'Float'): return ('String', str(v))
    elif t == 'Bool': return ('String', 'true' if v else 'false')
    elif t == 'Void': return ('String', 'void')
    
    elif t == 'List':
        parts = []
        for item in v: # item is ('Int', 2)
            # Вызываем to_string рекурсивно для каждого элемента
            s = builtin_to_string(env, [item])
            parts.append(s[1])
        return ('String', '[' + ', '.join(parts) + ']')
        
    elif t == 'Tuple':
        parts = []
        for item in v:
            s = builtin_to_string(env, [item])
            parts.append(s[1])
        return ('String', '(' + ', '.join(parts) + ')')
        
    elif t == 'Json': 
        return builtin_json_to_string(env, args)
        
    else: 
        raise RuntimeError(f"to_string не поддерживает тип {t}")

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
    if len(args) != 1 or args[0][0] != 'String':
        raise RuntimeError("ref требует 1 аргумент: имя переменной (строку)")
    var_name = args[0][1]
    try:
        env.get(var_name)
    except RuntimeError:
        raise RuntimeError(f"Невозможно взять ссылку: переменная '{var_name}' не найдена")
    return ('Ref', var_name)

@krust_builtin("deref")
def builtin_deref(env, args):
    if len(args) != 1 or args[0][0] != 'Ref':
        raise RuntimeError("deref требует 1 аргумент: ссылку (Ref)")
    var_name = args[0][1]
    return env.get(var_name)

@krust_builtin("set_ref")
def builtin_set_ref(env, args):
    if len(args) != 2 or args[0][0] != 'Ref':
        raise RuntimeError("set_ref требует 2 аргумента: (ссылка, новое_значение)")
    var_name = args[0][1]
    new_value = args[1]
    env.update(var_name, new_value)
    return ('Void', None)

# --- Запросы ---
def convert_krust_json_to_python(krust_json):
    result = {}
    for key, value in krust_json.items():
        result[key] = convert_krust_value_to_python(value)
    return result

def convert_krust_list_to_python(krust_list):
    result = []
    for item in krust_list:
        result.append(convert_krust_value_to_python(item))
    return result

def convert_krust_value_to_python(krust_value):
    if not isinstance(krust_value, tuple) and not isinstance(krust_value, list):
        return krust_value
    tp, val = krust_value
    if tp == 'String': return val
    elif tp == 'Int': return val
    elif tp == 'Float': return val
    elif tp == 'Bool': return val
    elif tp == 'List': return convert_krust_list_to_python(val)
    elif tp == 'Json': return convert_krust_json_to_python(val)
    elif tp == 'Void': return None
    else: return val

def convert_python_to_krust(py_value):
    if py_value is None: return ('Void', None)
    elif isinstance(py_value, str): return ('String', py_value)
    elif isinstance(py_value, bool): return ('Bool', py_value)
    elif isinstance(py_value, int): return ('Int', py_value)
    elif isinstance(py_value, float): return ('Float', py_value)
    elif isinstance(py_value, list): return ('List', [convert_python_to_krust(item) for item in py_value])
    elif isinstance(py_value, dict):
        result = {}
        for key, value in py_value.items():
            result[key] = convert_python_to_krust(value)
        return ('Json', result)
    else: return ('String', str(py_value))

@krust_builtin("request")
def builtin_request(env, args):
    if len(args) < 2:
        raise RuntimeError("request требует минимум 2 аргумента: (url, method)")
    url_t, url = args[0]
    if url_t != 'String': raise RuntimeError("Первый аргумент должен быть String (URL)")
    method_t, method = args[1]
    if method_t != 'String': raise RuntimeError("Второй аргумент должен быть String (метод)")
    method = method.upper()
    valid_methods = {'GET', 'POST', 'PUT', 'DELETE', 'PATCH', 'HEAD'}
    if method not in valid_methods:
        raise RuntimeError(f"Неверный метод: {method}. Допустимые: {', '.join(valid_methods)}")
    
    data = None; json_data = None
    if len(args) > 2:
        data_t, data_val = args[2]
        if data_t == 'Json': json_data = convert_krust_json_to_python(data_val)
        elif data_t == 'List': json_data = convert_krust_list_to_python(data_val)
        elif data_t == 'String': data = data_val
        elif data_t in ('Int', 'Float', 'Bool'): data = str(data_val)
        elif data_t != 'Void': raise RuntimeError(f"Неподдерживаемый тип данных: {data_t}")
    
    headers = {}
    if len(args) > 3:
        headers_t, headers_val = args[3]
        if headers_t == 'Json': headers = convert_krust_json_to_python(headers_val)
        elif headers_t != 'Void': raise RuntimeError("Заголовки должны быть Json или Void")
    
    if json_data is not None and 'Content-Type' not in headers:
        headers['Content-Type'] = 'application/json'
    
    try:
        response = None
        if method == 'GET': response = requests.get(url, headers=headers, timeout=30)
        elif method == 'POST':
            if json_data is not None: response = requests.post(url, json=json_data, headers=headers, timeout=30)
            else: response = requests.post(url, data=data, headers=headers, timeout=30)
        elif method == 'PUT':
            if json_data is not None: response = requests.put(url, json=json_data, headers=headers, timeout=30)
            else: response = requests.put(url, data=data, headers=headers, timeout=30)
        elif method == 'DELETE':
            if json_data is not None: response = requests.delete(url, json=json_data, headers=headers, timeout=30)
            else: response = requests.delete(url, data=data, headers=headers, timeout=30)
        elif method == 'PATCH':
            if json_data is not None: response = requests.patch(url, json=json_data, headers=headers, timeout=30)
            else: response = requests.patch(url, data=data, headers=headers, timeout=30)
        elif method == 'HEAD': response = requests.head(url, headers=headers, timeout=30)
        
        body_krust = ('String', response.text)
        content_type = response.headers.get('Content-Type', '').lower()
        if 'application/json' in content_type:
            try:
                body = response.json()
                body_krust = convert_python_to_krust(body)
            except: pass
        
        result_headers = {}
        for key, value in response.headers.items():
            result_headers[key] = ('String', str(value))
        
        result = {
            'status': ('Int', response.status_code),
            'headers': ('Json', result_headers),
            'body': body_krust,
            'error': ('Void', None)
        }
        return ('Json', result)
        
    except requests.exceptions.Timeout:
        return ('Json', {'status': ('Int', 0), 'headers': ('Json', {}), 'body': ('String', ''), 'error': ('String', 'Timeout')})
    except requests.exceptions.ConnectionError:
        return ('Json', {'status': ('Int', 0), 'headers': ('Json', {}), 'body': ('String', ''), 'error': ('String', 'Connection Error')})
    except requests.exceptions.RequestException as e:
        return ('Json', {'status': ('Int', 0), 'headers': ('Json', {}), 'body': ('String', ''), 'error': ('String', str(e))})
    except Exception as e:
        raise RuntimeError(f"Ошибка при выполнении запроса: {e}")

@krust_builtin("wget")
def builtin_wget(env, args):
    if len(args) < 1: raise RuntimeError("wget требует минимум 1 аргумент (URL)")
    url_t, url = args[0]
    if url_t != 'String': raise RuntimeError("Первый аргумент должен быть String (URL)")
    
    filename = None
    if len(args) > 1:
        filename_t, filename_val = args[1]
        if filename_t != 'String': raise RuntimeError("Второй аргумент должен быть String (путь сохранения)")
        filename = filename_val
    
    headers = {}
    if len(args) > 2:
        headers_t, headers_val = args[2]
        if headers_t == 'Json': headers = convert_krust_json_to_python(headers_val)
        elif headers_t != 'Void': raise RuntimeError("Заголовки должны быть Json или Void")
    
    if filename is None:
        parsed_url = urllib.parse.urlparse(url)
        filename = os.path.basename(parsed_url.path)
        if not filename: filename = f"download_{int(time.time())}"
    if '?' in filename: filename = filename.split('?')[0]
    if not filename or '.' not in filename:
        filename = filename or "download"
        filename += ".bin"
    
    filename = os.path.abspath(filename)
    os.makedirs(os.path.dirname(filename) if os.path.dirname(filename) else '.', exist_ok=True)
    
    print(f"\nСкачивание: {url}")
    print(f"Сохранение: {filename}")
    
    downloaded = 0; total_size = 0; start_time = time.time()
    temp_filename = filename + ".tmp"
    connection_lost = False; error_message = None
    
    try:
        response = requests.get(url, headers=headers, stream=True, timeout=30)
        response.raise_for_status()
        total_size = int(response.headers.get('content-length', 0))
        
        if os.path.exists(filename):
            if total_size > 0 and os.path.getsize(filename) == total_size:
                print(f"Файл уже существует: {filename}")
                return ('Json', {'success': ('Bool', True), 'filename': ('String', filename), 'size': ('Int', total_size), 'message': ('String', 'Файл уже существует'), 'error': ('Void', None)})
            base, ext = os.path.splitext(filename)
            counter = 1
            while os.path.exists(f"{base}_{counter}{ext}"): counter += 1
            filename = f"{base}_{counter}{ext}"
        
        with open(temp_filename, 'wb') as f:
            for chunk in response.iter_content(chunk_size=8192):
                if chunk:
                    f.write(chunk); downloaded += len(chunk)
                    if total_size > 0:
                        percent = (downloaded / total_size) * 100
                        bar_length = 40; filled_length = int(bar_length * downloaded // total_size)
                        bar = '█' * filled_length + '░' * (bar_length - filled_length)
                        elapsed = time.time() - start_time
                        speed = downloaded / elapsed if elapsed > 0 else 0
                        eta = (total_size - downloaded) / speed if speed > 0 else 0
                        downloaded_mb = downloaded / (1024 * 1024); total_mb = total_size / (1024 * 1024)
                        speed_mb = speed / (1024 * 1024)
                        sys.stdout.write(f'\r[{bar}] {percent:.1f}% ({downloaded_mb:.2f}/{total_mb:.2f} MB) {speed_mb:.2f} MB/s ETA: {eta:.1f}s    ')
                    else:
                        downloaded_mb = downloaded / (1024 * 1024)
                        sys.stdout.write(f'\rСкачано: {downloaded_mb:.2f} MB    ')
                    sys.stdout.flush()
        
        if os.path.exists(temp_filename):
            if os.path.exists(filename): os.remove(filename)
            os.rename(temp_filename, filename)
        
        elapsed = time.time() - start_time
        if total_size > 0:
            downloaded_mb = downloaded / (1024 * 1024); total_mb = total_size / (1024 * 1024)
            speed_mb = downloaded / (1024 * 1024) / elapsed if elapsed > 0 else 0
            bar = '█' * 40
            sys.stdout.write(f'\r[{bar}] 100.0% ({downloaded_mb:.2f}/{total_mb:.2f} MB) {speed_mb:.2f} MB/s Завершено за {elapsed:.1f}s\n')
        else:
            downloaded_mb = downloaded / (1024 * 1024)
            sys.stdout.write(f'\rСкачано: {downloaded_mb:.2f} MB за {elapsed:.1f}s\n')
        sys.stdout.flush()
        
        if os.path.exists(filename) and os.path.getsize(filename) > 0:
            print(f"Файл успешно сохранён: {filename} ({downloaded} байт)")
            return ('Json', {'success': ('Bool', True), 'filename': ('String', filename), 'size': ('Int', downloaded), 'time': ('Float', elapsed), 'message': ('String', f'Файл успешно скачан за {elapsed:.1f} секунд'), 'error': ('Void', None)})
        else: raise RuntimeError("Файл не был сохранён")
            
    except requests.exceptions.Timeout: error_message = "Timeout"; connection_lost = True
    except requests.exceptions.ConnectionError: error_message = "Connection Error"; connection_lost = True
    except requests.exceptions.HTTPError as e: error_message = f"HTTP Error {e.response.status_code}"; connection_lost = True
    except requests.exceptions.RequestException as e: error_message = f"Request Error: {str(e)}"; connection_lost = True
    except Exception as e: error_message = f"Unknown Error: {str(e)}"; connection_lost = True
    
    if connection_lost:
        if os.path.exists(temp_filename):
            try: os.remove(temp_filename)
            except: pass
        if os.path.exists(filename) and downloaded > 0:
            try: os.remove(filename)
            except: pass
        print(f"\nОШИБКА: {error_message}")
        return ('Json', {'success': ('Bool', False), 'filename': ('String', filename), 'size': ('Int', downloaded), 'error': ('String', error_message), 'message': ('Void', None)})

@krust_builtin("system_info")
def builtin_system_info(env, args):
    return ('Json', {"system_ver": platform.version(), "krust_version": VERSION})

# === Регулярные выражения ===
@krust_builtin("reg_match")
def builtin_reg_match(env, args):
    if len(args) != 2:
        raise RuntimeError("reg_match требует 2 аргумента: (выражение, строка)")

    reg_t, reg = args[0]
    string_t, string = args[1]

    if reg_t != 'String':
        raise RuntimeError("Выражение должно быть String")
    if string_t != 'String':
        raise RuntimeError("Строка должна быть String")

    matched = re.match(reg, string)
    if not matched:
        return ('List', [])  # пустой список — совпадений нет

    # matched.groups() — только группы (без всего совпадения)
    # matched.group(0) — всё совпадение
    groups = [matched.group(0)] + list(matched.groups())
    return ('List', [('String', g) for g in groups if g is not None])

# ==========================================
# 5. Интерпретатор с Traceback и FuncRef
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
        
        if node[0] == 'Ident': 
            name = node[1]
            # Сначала пробуем получить переменную
            try:
                return env.get(name)
            except RuntimeError:
                # Если переменной нет, проверяем, не функция ли это
                func_data = env.get_func(name)
                if func_data:
                    return ('FuncRef', func_data)
                # Если ни переменная, ни функция не найдены - пробрасываем ошибку
                raise RuntimeError(f"Переменная или функция '{name}' не найдена")

        if node[0] == 'VarDecl':
            _, type_name, var_name, value_node = node
            val_type, val = evaluate(value_node, env, current_frame)
            
            # Разрешаем объявлять переменные типа Func
            if type_name == 'Func' and val_type == 'FuncRef':
                 env.set(var_name, val)
                 return ('Void', None)
                 
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
            
            # Проверяем, является ли name встроенной функцией
            if name in BUILTINS:
                return BUILTINS[name](env, [evaluate(arg, env, current_frame) for arg in args])

            # Проверяем, является ли name определенной пользователем функцией
            func_data = env.get_func(name)
            
            # Если нет, возможно, это переменная, содержащая FuncRef (коллбэк)
            if not func_data:
                try:
                    val = env.get(name)
                    if val[0] == 'FuncRef':
                        func_data = val[1]
                    else:
                        raise RuntimeError(f"'{name}' не является функцией или коллбэком")
                except RuntimeError:
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
                return evaluate(body, new_env, f"функции '{name}'")
            except ReturnException as e:
                return e.value
            except KrustError as de:
                de.add_frame(f"функции '{name}'")
                raise

        raise RuntimeError(f"Неизвестный узел AST: {node}")
        
    except KrustError:
        raise
    except Exception as e:
        raise KrustError(str(e), current_frame)

def _bracket_balance(code):
    """Возвращает разницу открытых и закрытых скобок, игнорируя строки и комментарии."""
    depth = 0
    in_string = False
    in_comment = False
    escape = False
    i = 0
    while i < len(code):
        ch = code[i]

        if in_comment:
            if ch == '\n':
                in_comment = False
            i += 1
            continue

        if in_string:
            if escape:
                escape = False
            elif ch == '\\':
                escape = True
            elif ch == '"':
                in_string = False
            i += 1
            continue

        if ch == '/' and i + 1 < len(code) and code[i+1] == '/':
            in_comment = True
            i += 2
            continue

        if ch == '"':
            in_string = True
        elif ch in '([{':
            depth += 1
        elif ch in ')]}':
            depth -= 1

        i += 1
    return depth

# ==========================================
# 6. Точка входа
# ==========================================
def run_krust(code, main_filename=None, main_dirname=None, main_libname=None):
    global GLOBAL_KRUST_ENV

    env = Environment()
    GLOBAL_KRUST_ENV = env

    if main_filename is not None:
        env.set('__FILENAME__', ('String', main_filename))
    if main_dirname is not None:
        env.set('__DIRNAME__',  ('String', main_dirname))
    if main_libname is not None:
        env.set('__LIBNAME__',  ('String', main_libname))

    env.set('OS', ('String', platform.system()))

    try:
        ast = parse(code)
        for node in ast:
            evaluate(node, env, "<main>")
    except SyntaxError as e:
        print(f"\n[SYNTAX ERROR] {e}")
    except KrustError as e:
        print(e)
    except Exception as e:
        print(f"[KRUST ERROR] Неожиданная ошибка Python: {e}")

def run_repl():
    global GLOBAL_KRUST_ENV

    env = Environment()
    GLOBAL_KRUST_ENV = env

    env.set('__FILENAME__', ('String', '*repl'))
    env.set('__DIRNAME__',  ('String', '*repl'))
    env.set('__LIBNAME__',  ('String', '*repl'))
    env.set('OS', ('String', platform.system()))

    buffer = []
    while True:
        prompt = "REPL> " if not buffer else "...   "
        try:
            line = input(prompt)
        except EOFError:
            break

        if not buffer and line.lower().strip() == "exit":
            break

        buffer.append(line)
        code = "\n".join(buffer)

        # Если скобки не сбалансированы — ждём продолжения
        if _bracket_balance(code) > 0:
            continue

        buffer.clear()

        try:
            ast = parse(code)
            for node in ast:
                evaluate(node, env, "<main>")
        except SyntaxError as e:
            print(f"\n[SYNTAX ERROR] {e}")
        except KrustError as e:
            print(e)
        except Exception as e:
            print(f"[KRUST ERROR] Неожиданная ошибка Python: {e}")

if __name__ == "__main__":
    argparser = argparse.ArgumentParser('Krust Language', description='A Functional Programming Language')
    argparser.add_argument('file', nargs='?', help='Файл для исполнения')
    args = argparser.parse_args()

    if not args.file:
        run_repl()
        exit(0)

    abs_main = os.path.abspath(args.file)

    __FILENAME__ = os.path.basename(abs_main)
    __DIRNAME__  = os.path.dirname(abs_main)
    __LIBNAME__  = os.path.splitext(__FILENAME__)[0]

    with open(args.file, 'r', encoding='utf-8') as f:
        krust_code = f.read()

    start = time.time()
    run_krust(krust_code, __FILENAME__, __DIRNAME__, __LIBNAME__)
    end = time.time()
    print(f"\nВсего выполнено за {end - start:.4f} сек.")