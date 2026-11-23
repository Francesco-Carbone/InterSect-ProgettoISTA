"""
Funzioni di utilita' pure del motore di campionamento (CR3 - refactoring).

Raccoglie in un unico modulo le funzioni che lavorano solo su testo SMT-LIB o su valori:
nessuna usa il solver Z3, scrive file di lavoro o conserva uno stato. Prima erano sparse
in solver_utils.py e solver_utils_typed.py, che le importano da qui.

- parsing SMT-LIB: tokenizzazione, pulizia dei comandi, estrazione delle variabili libere tipizzate;
- formattazione e normalizzazione di valori del modello (letterali SMT, stringhe);
- conteggi e insiemi su intervalli (multiinsiemi, normalizzazione delle maschere);
- codifica delle stringhe (indice -> stringa).
"""
import re
from collections import Counter

import numpy as np


def _tokenize_smt2(content: str) -> list[str]:
    """
    Split SMT2 content into top-level s-expressions and atoms,
    correctly handling:
      - nested parentheses
      - quoted symbols |...|
      - string literals "..."
      - line comments ;...
    """
    tokens = []
    i = 0
    n = len(content)

    while i < n:
        ch = content[i]

        # Skip whitespace between top-level tokens
        if ch in ' \t\n\r':
            i += 1
            continue

        # Line comment — skip to end of line
        if ch == ';':
            while i < n and content[i] != '\n':
                i += 1
            continue

        # Quoted symbol |...|
        if ch == '|':
            start = i
            i += 1
            while i < n and content[i] != '|':
                i += 1
            i += 1  # consume closing |
            tokens.append(content[start:i])
            continue

        # String literal "..."
        if ch == '"':
            start = i
            i += 1
            while i < n:
                if content[i] == '\\':
                    i += 2  # escaped character
                elif content[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            tokens.append(content[start:i])
            continue

        # S-expression: read until matching closing paren
        if ch == '(':
            start = i
            depth = 0
            while i < n:
                c = content[i]
                if c == ';':
                    while i < n and content[i] != '\n':
                        i += 1
                    continue
                if c == '|':
                    i += 1
                    while i < n and content[i] != '|':
                        i += 1
                elif c == '"':
                    i += 1
                    while i < n:
                        if content[i] == '\\':
                            i += 2
                            continue
                        if content[i] == '"':
                            break
                        i += 1
                elif c == '(':
                    depth += 1
                elif c == ')':
                    depth -= 1
                    if depth == 0:
                        i += 1
                        break
                i += 1
            tokens.append(content[start:i])
            continue

        # Bare atom (keyword, symbol, number)
        start = i
        while i < n and content[i] not in ' \t\n\r();"|\n':
            i += 1
        tokens.append(content[start:i])

    return tokens


def _get_command_name(token: str) -> str | None:
    """Extract the leading keyword from an s-expression token."""
    m = re.match(r'^\(\s*([\w-]+)', token)
    return m.group(1).lower() if m else None


# Commands that z3.parse_smt2_string understands
_ALLOWED_COMMANDS = {
    "declare-fun",
    "declare-const",
    "declare-sort",
    "declare-datatypes",
    "define-fun",
    "define-fun-rec",
    "define-funs-rec",
    "define-sort",
    "assert",
    "set-logic",
}


def _strip_smt2_commands_2(smt2_content: str) -> str:
    """
    Robustly strips all commands that z3.parse_smt2_string cannot handle,
    using a proper tokenizer instead of regex. Handles:
      - push/pop and all incremental commands
      - set-info / set-option with nested parens or multiline values
      - multiple check-sat blocks (collects ALL assertions, not just pre-first)
      - quoted symbols |...| and string literals "..."
      - line comments
    """
    tokens = _tokenize_smt2(smt2_content)
    kept = [t for t in tokens if _get_command_name(t) in _ALLOWED_COMMANDS]
    return "\n".join(kept)


def extract_free_vars_with_type_from_smt2_file(file_path):
    free_vars = []
    with open(file_path, "r") as f:
        for line in f:
            # Match zero-arg declare-fun: (declare-fun <name> () <type>)
            m_fun = re.match(r"\(declare-fun\s+(\w+)\s+\(\s*\)\s+(.+)\)", line)
            # Match declare-const: (declare-const <name> <type>)
            m_const = re.match(r"\(declare-const\s+(\w+)\s+(.+)\)", line)
            if m_fun:
                name = m_fun.group(1)
                var_type = m_fun.group(2).strip()
                free_vars.append((name, var_type))
            elif m_const:
                name = m_const.group(1)
                var_type = m_const.group(2).strip()
                free_vars.append((name, var_type))
    return free_vars


def uniform_multiset(domain_start, domain_end, size):
    X = np.random.uniform(0, 1, size)   # <-- normalized domain
    X = np.round(X, 6)
    return Counter(X)


def multiset_from_intervals_2(intervals, min_value, max_value):
    S = Counter()

    for a, b in intervals:
        try:   
            num_samples = max(5, int(1000 * (b - a) / (max_value - min_value)))
            # if not b-a > 0 and num_samples < b-a:
            #     num_samples = b-a
            # print("num_samples =", num_samples, "for interval of size", b - a)
            norm_a = (a - min_value) / (max_value - min_value)
            norm_b = (b - min_value) / (max_value - min_value)
            pts = np.linspace(norm_a, norm_b, num_samples)
        except Exception as e:
            print("\n--- ERROR IN INTERVAL ---")
            print("a =", a, type(a))
            print("b =", b, type(b))
            print("num_samples =", num_samples)
            raise e
        for x in pts:
            S[round(x,16)] += 1
    return S


def expand_multiset(M):
    arr = []
    for x, count in M.items():
        arr.extend([x] * count)
    return np.array(arr)


TOTAL_STRINGS = sum(26**k for k in range(1, 55))


def index_to_string(i: int) -> str:
    """
    Returns the string at 0-based position i in the lexicographic enumeration
    of all strings over {a..z} with length 1 to 54.

    Order: a, b, ..., z, aa, ab, ..., az, ba, ..., zz, aaa, ...

    Indices >= TOTAL_STRINGS are clamped via modulo to stay in range.
    """
    if i < 0:
        raise ValueError("Index must be non-negative.")

    i = i % TOTAL_STRINGS  # clamp out-of-range indices

    ALPHABET = 'abcdefghijklmnopqrstuvwxyz'
    MAX_LEN  = 54

    # --- Step 1: determine the length of the target string ---
    length = 1
    count  = 26          # number of strings of current length (26^length)

    while i >= count:
        if length == MAX_LEN:
            raise ValueError(f"Index {i} exceeds the language (max length {MAX_LEN}).")
        i     -= count
        length += 1
        count  = 26 ** length

    # --- Step 2: decode the offset `i` in base-26 into `length` characters ---
    chars = []
    for _ in range(length):
        chars.append(ALPHABET[i % 26])
        i //= 26

    return ''.join(reversed(chars))


BITVEC_RE = re.compile(r"^\(_\s+BitVec\s+(\d+)\)$")


def _format_literal(value, var_type):
    if var_type == "Bool":
        return "true" if value else "false"

    bitvec_match = BITVEC_RE.match(var_type)
    if bitvec_match:
        return f"(_ bv{int(value)} {int(bitvec_match.group(1))})"

    if var_type == "String":
        escaped = str(value).replace("\\", "\\\\").replace('"', '\\"')
        return f'"{escaped}"'

    return str(value)


def _normalize_model_value(z3_value, var_type):
    if var_type == "String":
        value = str(z3_value)
        if value.startswith('"') and value.endswith('"'):
            return value[1:-1]
        return value
    if var_type == "Bool":
        return str(z3_value).lower() == "true"
    return int(str(z3_value))


def _unescape_smt_string(value):
    return bytes(value, "utf-8").decode("unicode_escape")


def _normalize_mask_intervals(mask, domain_lb, domain_ub):
    if not mask:
        return []

    clipped = []
    for start, end in sorted(mask, key=lambda interval: interval[0]):
        start = max(domain_lb, start)
        end = min(domain_ub, end)
        if start < end:
            clipped.append((start, end))

    if not clipped:
        return []

    merged = [clipped[0]]
    for start, end in clipped[1:]:
        last_start, last_end = merged[-1]
        if start <= last_end:
            merged[-1] = (last_start, max(last_end, end))
        else:
            merged.append((start, end))
    return merged
