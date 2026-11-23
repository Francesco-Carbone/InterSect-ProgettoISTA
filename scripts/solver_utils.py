import random, re, shutil, itertools, z3, pandas as pd, uuid, time
from pathlib import Path
from scipy.stats import ks_2samp, kstest, mannwhitneyu
from tqdm.auto import tqdm

from smt_utils import (
    _strip_smt2_commands_2,
    expand_multiset,
    index_to_string,
    multiset_from_intervals_2,
    uniform_multiset,
)

"""
Libreria di utilità e motore di campionamento ibrido per la verifica formale basata su SMT (Z3). 
Fornisce funzioni per il partizionamento e l'esplorazione dello spazio degli stati, 
la generazione e la gestione di maschere di copertura per domini interi e stringhe, 
l'esecuzione di query e l'estrazione di modelli tramite Z3, nonché l'applicazione 
di test statistici per la verifica dell'uniformità dei campioni.
"""

def hybrid_state_space_sampler(free_vars, smt_filepath, theta, coverage):
##################  hybrid state-space sampler  ##################
    S = set()
    E = set()
    L = set()
    solver_result = {}
    n = 2**256
    
    #make a copy of the file and work on the copy at each iteration to avoid modifying the original SMT formula
    tmp_dir = Path(__file__).parent.parent / "tmp"
    tmp_dir.mkdir(parents=True, exist_ok=True)
    tmp_filepath = tmp_dir / f"tmp_{uuid.uuid4().hex}.smt2"
    shutil.copy2(smt_filepath, tmp_filepath)
    
    start_time = time.perf_counter()
    for free_var in free_vars:
        partitionVariable(E, L, smt_filepath, free_var, theta=theta)
        
    if E :
        assignments = list(get_assignment_for_E(E))
        if len(assignments) > theta:
            print(f"Too many assignments for E ({len(assignments)}), sampling {theta} random assignments...")
            assignments = random.sample(assignments, theta)
        if assignments is not None:
            for assignment in assignments:
                
                add_e_assignment(assignment, tmp_filepath) # Add assignment of brute force variable to SMT formula 
                mask_var_pairs = []
                if L :
                    # print(f"Variables in E and L")
                    for (var, lb, ub) in tqdm(L, desc="Generating masks..."):
                        mask = create_mask_with_coverage(lb, ub, target_coverage=coverage) # generate mask
                        mask_var_pairs.append((var, mask))
                        n = min(n, len(mask)) 
                        # add bands to SMT formula
                        for (band_lb, band_ub) in mask:
                            add_band(band_lb, band_ub, var, tmp_filepath)
                    for i in range(n):
                        status, model = run_z3_and_get_model(tmp_filepath)
                        
                        if status == "UNSAT" or status == "UNKNOWN":
                            partial_time = time.perf_counter() - start_time
                            start_time = time.perf_counter()
                            save_model(solver_result, model, free_vars, tmp_filepath, status, assignment, mask_var_pairs, partial_time)
                            
                            break
                        if status == "SAT":
                            partial_time = time.perf_counter() - start_time
                            start_time = time.perf_counter()
                            save_sat_model(solver_result, model, free_vars, tmp_filepath, status, mask_var_pairs, partial_time)
                            # remove bands used by model
                            remove_used_band(model, L, tmp_filepath, mask_var_pairs) 
                            # add blocking clause to prevent same model
                            prevent_same_model(model, L, tmp_filepath)
                            # save model in set S
                            S.add(frozenset(model.items()))
                else:
                    # print(f"Variables in E")
                    status, model = run_z3_and_get_model(tmp_filepath)
                    
                    if status == "UNSAT" or status == "UNKNOWN":
                        partial_time = time.perf_counter() - start_time
                        start_time = time.perf_counter()
                        save_model(solver_result, model, free_vars, tmp_filepath, status, assignment, mask_var_pairs, partial_time)
                    if status == "SAT":
                        partial_time = time.perf_counter() - start_time
                        start_time = time.perf_counter()
                        save_sat_model(solver_result, model, free_vars, tmp_filepath, status, mask_var_pairs, partial_time)
                        # remove bands used by model
                        # remove_used_band(model, L, tmp_filepath) 
                        # add blocking clause to prevent same model
                        # prevent_same_model(model, L, tmp_filepath)
                        # save model in set S
                        S.add(frozenset(model.items()))
    if not E and L :
        # print(f"Variables in L")
        mask_var_pairs = []
        for (var, lb, ub) in tqdm(L, desc="Generating masks..."):
            mask = create_mask_with_coverage(lb, ub, target_coverage=coverage) # generate mask
            mask_var_pairs.append((var, mask))
            n = min(n, len(mask)) 
            # add bands to SMT formula
            for (band_lb, band_ub) in mask:
                add_band(band_lb, band_ub, var, tmp_filepath)
        print("Masks generated")
        for i in range(n):
            status, model = run_z3_and_get_model(tmp_filepath)
            
            if status == "UNSAT" or status == "UNKNOWN":
                partial_time = time.perf_counter() - start_time
                start_time = time.perf_counter()
                save_model(solver_result, model, free_vars, tmp_filepath, status, None, mask_var_pairs, partial_time)
                break
            if status == "SAT":
                partial_time = time.perf_counter() - start_time
                start_time = time.perf_counter()
                save_sat_model(solver_result, model, free_vars, tmp_filepath, status, mask_var_pairs, partial_time)
                # remove bands used by model
                remove_used_band(model, L, tmp_filepath, mask_var_pairs) 
                # add blocking clause to prevent same model
                prevent_same_model(model, L, tmp_filepath)
                # save model in set S
                S.add(frozenset(model.items()))  
    ##################  hybrid state-space sampler  ##################
    #save solver_result on csv file
    df = pd.DataFrame(solver_result)
    # Build output directory mirroring the benchmark folder structure
    benchmark_dir = Path(smt_filepath).parent
    results_dir = benchmark_dir.parent / (benchmark_dir.name + "_results" + "_cov" + str(coverage) )
    results_dir.mkdir(parents=True, exist_ok=True)
    # Save CSV
    csv_filename = Path(smt_filepath).stem + ".csv"
    df.to_csv(results_dir / csv_filename, index=False)
    return S

def save_model(solver_result, model, free_vars, tmp_filepath, status, assignment, mask_var_pairs, partial_time):
    """
    Saves a row for UNSAT or UNKNOWN results.
    Free vars from assignment carry their assigned value;
    all other free vars are saved as None.

    Args:
        solver_result:   dict accumulating results (column -> list of values)
        model:           Z3 model dict (ignored for UNSAT/UNKNOWN, kept for signature consistency)
        free_vars:       list of all free variable names in the formula
        tmp_filepath:    path to the tmp .smt2 file used in this iteration
        status:          "UNSAT" or "UNKNOWN"
        assignment:      dict {var_name: value} of variables fixed by E-assignment
        mask_var_pairs:  list of (var, lb, ub) tuples describing the active mask bands
    """
    if status not in ("UNSAT", "UNKNOWN"):
        return

    # Normalize assignment to a plain dict regardless of how it's passed in
    if isinstance(assignment, frozenset):
        assignment_dict = dict(assignment)
    elif isinstance(assignment, dict):
        assignment_dict = assignment
    else:
        assignment_dict = {}

    free_vars_set = set(free_vars)

    # Ensure metadata columns exist
    for meta_key in ("filename", "status", "mask_var_pairs", "time"):
        if meta_key not in solver_result:
            solver_result[meta_key] = [None] * (len(next(iter(solver_result.values()))) if solver_result else 0)

    # Ensure all free var columns exist
    for var in free_vars_set:
        if var not in solver_result:
            solver_result[var] = [None] * (len(next(iter(solver_result.values()))) if solver_result else 0)

    # Append values: assignment value if var was fixed, None otherwise
    for var in free_vars_set:
        solver_result[var].append(assignment_dict.get(var, None))

    solver_result["filename"].append(Path(tmp_filepath).name)
    solver_result["status"].append(status)
    solver_result["mask_var_pairs"].append(list(mask_var_pairs) if mask_var_pairs is not None else None)
    solver_result["time"].append(partial_time) 

def save_sat_model(result, model_dict, free_vars, tmp_filepath, status, mask_var_pairs, partial_time):
    free_vars_set = set(free_vars)

    # Ensure metadata columns exist
    for meta_key in ("filename", "status", "mask_var_pairs", "time"):
        if meta_key not in result:
            result[meta_key] = [None] * (len(next(iter(result.values()))) if result else 0)

    if model_dict is None:
        for key in result:
            result[key].append(None)
        # Overwrite the Nones just appended for metadata
        result["filename"][-1] = Path(tmp_filepath).name
        result["status"][-1] = status
        result["mask_var_pairs"][-1] = list(mask_var_pairs) if mask_var_pairs is not None else None
        return result

    # Filter model_dict to only free vars
    filtered = {k: v for k, v in model_dict.items() if k in free_vars_set}

    # Ensure all free vars exist as keys in result
    for var in free_vars_set:
        if var not in result:
            result[var] = [None] * (len(next(iter(result.values()))) if result else 0)

    # Append values for this iteration
    for var in result:
        if var in ("filename", "status", "mask_var_pairs", "time"):
            continue
        result[var].append(filtered.get(var, None))

    result["filename"].append(Path(tmp_filepath).name)
    result["status"].append(status)
    result["mask_var_pairs"].append(list(mask_var_pairs) if mask_var_pairs is not None else None)
    result["time"].append(partial_time)  # added


    return result

# def save_sat_model(result, model_dict, free_vars):
#     if model_dict is None:
#         # append None for all existing columns
#         for key in result:
#             result[key].append(None)
#         return result
#     # First, ensure all keys exist
#     for var in model_dict:
#         if var not in result:
#             result[var] = [None] * (len(next(iter(result.values()))) if result else 0)
#     # Append values for this iteration
#     for var in result:
#         if var in model_dict:
#             val = model_dict[var]
#             if isinstance(val, list):
#                 result[var].append(val)
#             else:
#                 result[var].append(val)
#         else:
#             result[var].append(None)
#     return result

def remove_used_band(model, L, file_path, mask_var_pairs):
    with open(file_path, 'r') as f:
        content = f.read()

    vars_in_L = {var for var, lb, ub in L}

    # Build a quick lookup: var_name -> index in mask_var_pairs
    mask_index = {var: i for i, (var, mask) in enumerate(mask_var_pairs)}

    for var_name, z3_value in model.items():
        if var_name not in vars_in_L:
            continue

        value = int(str(z3_value))

        band_pattern = re.compile(
            rf'\s*\(and\s+\(>=\s+{re.escape(var_name)}\s+(\d+)\)\s+\(<\s+{re.escape(var_name)}\s+(\d+)\)\)'
        )

        or_block_pattern = re.compile(
            rf'\(assert\s+\(or\s+(?:\s*\(and\s+\(>=\s+{re.escape(var_name)}\s+\d+\)\s+\(<\s+{re.escape(var_name)}\s+\d+\)\))+\s*\)\)',
            re.MULTILINE
        )

        def remove_band_from_block(or_block_match):
            block = or_block_match.group(0)

            def replace(m):
                lb = int(m.group(1))
                ub = int(m.group(2))
                if lb <= value < ub:
                    # Remove from mask_var_pairs too
                    if var_name in mask_index:
                        idx = mask_index[var_name]
                        var, mask = mask_var_pairs[idx]
                        mask_var_pairs[idx] = (var, [b for b in mask if b != (lb, ub)])
                    return ''
                return m.group(0)

            return band_pattern.sub(replace, block)

        content = or_block_pattern.sub(remove_band_from_block, content)

    with open(file_path, 'w') as f:
        f.write(content)
# def remove_used_band(model, L, file_path, mask_var_pairs):
#     """
#     Per ogni variabile nel model presente in L, rimuove la banda (and (>= var LB) (< var UB))
#     che contiene il valore assunto dalla variabile.
#     Rimuove solo dalle clausole (assert (or ...)) e non dalla formula principale.
#     """
#     with open(file_path, 'r') as f:
#         content = f.read()

#     vars_in_L = {var for var, lb, ub in L}

#     for var_name, z3_value in model.items():
#         if var_name not in vars_in_L:
#             continue

#         value = int(str(z3_value))

#         band_pattern = re.compile(
#             rf'\s*\(and\s+\(>=\s+{re.escape(var_name)}\s+(\d+)\)\s+\(<\s+{re.escape(var_name)}\s+(\d+)\)\)'
#         )

#         # Matches only (assert (or ... )) blocks
#         or_block_pattern = re.compile(
#             rf'\(assert\s+\(or\s+(?:\s*\(and\s+\(>=\s+{re.escape(var_name)}\s+\d+\)\s+\(<\s+{re.escape(var_name)}\s+\d+\)\))+\s*\)\)',
#             re.MULTILINE
#         )

#         def remove_band_from_block(or_block_match):
#             block = or_block_match.group(0)

#             def replace(m):
#                 lb = int(m.group(1))
#                 ub = int(m.group(2))
#                 return '' if lb <= value < ub else m.group(0)

#             return band_pattern.sub(replace, block)

#         content = or_block_pattern.sub(remove_band_from_block, content)

#     with open(file_path, 'w') as f:
#         f.write(content)


def prevent_same_model(model, L, file_path):
    """
    Aggiunge una blocking clause considerando solo le variabili presenti in L.
    (assert (not (and (= var1 val1) (= var2 val2) ...)))
    """
    with open(file_path, 'r') as f:
        content = f.read()

    # Estrai solo le variabili presenti in L
    vars_in_L = {var for var, lb, ub in L}

    equalities = ' '.join(
        f'(= {var_name} {int(str(z3_value))})'
        for var_name, z3_value in model.items()
        if var_name in vars_in_L
    )

    if not equalities:
        return  # Nessuna variabile in L, niente da aggiungere

    blocking_clause = f'(assert (not (and {equalities})))\n'

    # Inserisci prima del primo (check-sat)
    lines = content.splitlines(keepends=True)
    first_checksat_index = next(
        (i for i, l in enumerate(lines) if l.strip().startswith('(check-sat)')),
        None
    )

    if first_checksat_index is None:
        content += blocking_clause
    else:
        lines.insert(first_checksat_index, blocking_clause)
        content = ''.join(lines)

    with open(file_path, 'w') as f:
        f.write(content)

def run_z3_and_get_model(smt_filepath, timeout_ms=None):
    """Returns (status, model_dict) where status is 'SAT', 'UNSAT', or 'UNKNOWN'."""
    with open(smt_filepath, 'r') as f:
        smt2_content = f.read()

    smt2_clean = _strip_smt2_commands_2(smt2_content)
    # smt2_clean = _strip_smt2_commands_2(smt2_content)

    solver = z3.Solver()
    if timeout_ms is not None:
        solver.set(timeout=int(timeout_ms))
    assertions = z3.parse_smt2_string(smt2_clean)
    solver.add(assertions)

    result = solver.check()
    print(f"Z3 result: {result}")
    if result == z3.sat:
        model = solver.model()
        model_dict = {model[i].name(): model[model[i]] for i in range(len(model))}
        return "SAT", model_dict
    elif result == z3.unsat:
        return "UNSAT", None
    else:
        return "UNKNOWN", None


    
def get_assignment_for_E(E):
    ranges = [(var, list(range(lb, ub + 1))) for (var, lb, ub) in E]
    var_names = [r[0] for r in ranges]
    val_lists = [r[1] for r in ranges]
    total = 1
    for vals in val_lists:
        total *= len(vals)
    print(f"Total assignments for E: {total}")
    for combo in itertools.product(*val_lists):
        yield dict(zip(var_names, combo))  # yield invece di return

def add_e_assignment(assignment, file_path):
    with open(file_path, "r") as f:
        content = f.read()

    # Rimuovi eventuali assignment precedenti
    content = re.sub(
        r'\(assert\s+\(and\s+(?:\(=\s+\w[\w@]*\s+\d+\)\s*)+\)\)\n?',
        '',
        content
    )

    # Build the SMT-LIB assert for the assignment
    clauses = [f"(= {var} {val})" for var, val in assignment.items()]
    assignment_assert = "(assert (and\n    " + "\n    ".join(clauses) + "\n))\n"

    # Inserisci prima del primo (check-sat)
    lines = content.splitlines(keepends=True)
    first_checksat_index = next(
        (i for i, l in enumerate(lines) if l.strip().startswith("(check-sat")),
        None
    )

    if first_checksat_index is None:
        content += assignment_assert
    else:
        lines.insert(first_checksat_index, assignment_assert)
        content = "".join(lines)

    with open(file_path, "w") as f:
        f.write(content)

def add_band(lb_band, ub_band, free_var, file_path):
    new_clause = f"(and (>= {free_var} {lb_band}) (< {free_var} {ub_band}))"

    with open(file_path, "r") as f:
        content = f.read()

    # Cerca un assert OR esistente per questa variabile
    # pattern = re.compile(
    #     rf'\(assert\s+\(or\s+((?:\(and\s+\(>=\s+{re.escape(free_var)}\s+\d+\)\s+\(<\s+{re.escape(free_var)}\s+\d+\)\)\s*)+)\)\)',
    #     re.MULTILINE
    # )
    pattern = re.compile(
        rf'\(assert\s+\(or\s+((?:\(and\s+\(>=\s+{re.escape(free_var)}\s+-?\d+\)\s+\(<\s+{re.escape(free_var)}\s+-?\d+\)\)\s*)+)\)\)',
        re.DOTALL # DOTALL aiuta a gestire meglio i ritorni a capo se presenti
    )

    match = pattern.search(content)

    if match:
        # Aggiungi il nuovo clause all'OR esistente
        existing_clauses = match.group(1).strip()
        new_assert = f'(assert (or\n  {existing_clauses}\n  {new_clause}\n))'
        content = content[:match.start()] + new_assert + content[match.end():]
    else:
        # Prima banda per questa variabile: crea l'assert OR
        new_assert = f'(assert (or\n  {new_clause}\n))'

        # Inserisci prima del primo check-sat
        lines = content.splitlines(keepends=True)
        first_checksat_index = next(
            (i for i, l in enumerate(lines) if l.strip().startswith("(check-sat")),
            None
        )

        if first_checksat_index is None:
            content += new_assert + "\n"
        else:
            lines.insert(first_checksat_index, new_assert + "\n")
            content = "".join(lines)

    with open(file_path, "w") as f:
        f.write(content)

# def add_band(lb_band, ub_band, free_var, file_path):
#     band_assert = f"(assert (and (>= {free_var} {lb_band}) (< {free_var} {ub_band})))\n"

#     # Read original content
#     with open(file_path, "r") as f:
#         lines = f.readlines()

#     # Find the first (check-sat)
#     first_checksat_index = None
#     for i, line in enumerate(lines):
#         if line.strip().startswith("(check-sat"):
#             first_checksat_index = i
#             break

#     if first_checksat_index is None:
#         # If no check-sat found, append at the end
#         lines.append(band_assert)
#     else:
#         # Insert band_assert right before the first check-sat
#         lines = (
#             lines[:first_checksat_index]
#             + [band_assert]
#             + lines[first_checksat_index:]
#         )

#     # Write back to the file
#     with open(file_path, "w") as f:
#         f.writelines(lines)


    
def partitionVariable(E: set,L: set,file_path, free_var, theta=1000):

    with open(file_path, "r") as f:
        content = f.read()
    # Pattern per catturare >=, >, <=, < anche con valori negativi
    pattern = fr'\(\s*(>=|>|<=|<)\s+{free_var}\s+(-?[0-9]+)\s*\)'
    matches = re.findall(pattern, content)

    # Default bounds uint256
    # lb = -2**255
    # ub = 2**256 - 1
    # Default bounds int256
    lb = 0
    ub = 2**256 - 1
    for op, val in matches:
        val = int(val)
        if op in ('>=', '>'):
            lb = max(lb, val + (1 if op == '>' else 0))
        elif op in ('<=', '<'):
            ub = min(ub, val - (1 if op == '<' else 0))

    # Verifica se il range è piccolo
    if ub >= lb and (ub - lb) <= theta:
        E.add((free_var, lb, ub))
    else:
        L.add((free_var, lb, ub))


def wrap(x, range_size, min_value):
    """Wrap integer x into [min_value, max_value] using modular arithmetic."""
    return min_value + ((x - min_value) % range_size)


def std_generator(min_value, max_value, width, num_intervals, range_size):
    intervals = []
    for _ in range(num_intervals):
        # Randomly select start in [min_value, max_value]
        start = random.randint(min_value, max_value)
        # Compute end using wrapping addition
        end = wrap(start + width, range_size, min_value)
        # Handle wrapped intervals that cross the boundary; normalize as two cases:
        # 1. Simple non-wrapping interval: start <= end
        # 2. Wrapping interval: start > end → split into two intervals
        if start <= end:
            intervals.append((start, end))
        else:
            # Wrapped interval; becomes two intervals:
            # [start, max_value] and [min_value, end]
            intervals.append((start, max_value))
            intervals.append((min_value, end))
    return intervals

# ------------------------------------------------------------------------------------------------------


# ------------------------------------------------------------------------------------------------------


# ------------------------------------------------------------------------------------------------------


# ------------------------------------------------------------------------------------------------------


def kolmogorov_smirnov_test(intervals, min_value, max_value, band_width, alpha=0.05):
    S_real = multiset_from_intervals_2(intervals, min_value, max_value)
    S_ideal = uniform_multiset(min_value, max_value, sum(S_real.values()))
    
    R = expand_multiset(S_real)
    I = expand_multiset(S_ideal)
    
    if band_width == 1:
        U, p = mannwhitneyu(R, I, alternative='two-sided')
        distribution_ok = p > 0.05
    else:
        D, p = ks_2samp(R, I)
        distribution_ok = D < 0.10 and p > 0.05
    return distribution_ok

# ----------------------------------------------STRING--------------------------------------------------------


def sample_interval(start: int, end: int, n: int) -> list[str]:
    """
    Uniformly samples n integers from [start, end] (inclusive)
    and returns their corresponding strings.

    - If n >= number of integers in the interval, all integers are returned.
    - Samples are always inclusive of both endpoints.
    """
    if start > end:
        raise ValueError(f"start ({start}) must be <= end ({end}).")
    if n <= 0:
        raise ValueError("n must be positive.")

    interval_size = end - start + 1

    if n >= interval_size:
        # Return every integer in the interval
        indices = range(start, end + 1)
    else:
        # Spread n points uniformly across [start, end], always including both endpoints
        indices = [
            round(start + i * (interval_size - 1) / (n - 1))
            for i in range(n)
        ] if n > 1 else [start]

    return [index_to_string(idx) for idx in indices]


def sample_intervals(intervals: list[tuple[int, int]], n: int) -> list[list[str]]:
    """
    Applies sample_interval to a list of (start, end) intervals.
    Returns a list of string lists, one per interval.
    """
    return [sample_interval(start, end, n) for start, end in intervals]

def create_string_mask_with_coverage(min_value, max_value, target_coverage, numStringSamples, delta):
    if min_value > max_value:
        raise ValueError("min_value must be <= max_value")
    cardinality = max_value - min_value + 1
    band_width = max(1, int(cardinality * delta))  # 0.12% del dominio
    if band_width == 1:
        min_intervals = int(target_coverage / band_width) - 10
    else:
        min_intervals = int((target_coverage / 100) / delta)

    distribution_ok = False
    iteration = 0
    
    while (
        not distribution_ok or
        (mask_coverage > target_coverage + 2) or
        (mask_coverage < target_coverage - 2)):
        # ---- Generate intervals ----
        intervals = std_generator(min_value, max_value, band_width, min_intervals, cardinality)
        
        # ---- Merge intervals ----
        intervals.sort(key=lambda x: x[0])
        merged = []

        for interval in intervals:
            if not merged:
                merged.append(interval)
            else:
                last_start, last_end = merged[-1]
                curr_start, curr_end = interval

                if curr_start <= last_end:  # overlap
                    merged[-1] = (last_start, max(last_end, curr_end))
                else:
                    merged.append(interval)
        # ---- Calculate mask coverage ----
        mask_coverage = sum(e - s for s,e in merged)/(max_value - min_value)
        mask_coverage = mask_coverage*100

        S_real = multiset_from_intervals_2(intervals, min_value, max_value)
        S_ideal = uniform_multiset(min_value, max_value, sum(S_real.values()))
        
        R = expand_multiset(S_real)
        I = expand_multiset(S_ideal)
        
        # SMALL_SAMPLE_THRESHOLD = 50
        # if len(R) < SMALL_SAMPLE_THRESHOLD or len(I) < SMALL_SAMPLE_THRESHOLD:
        
        if band_width == 1:
            U, p = mannwhitneyu(R, I, alternative='two-sided')
            distribution_ok = p > 0.05
        else:
            D, p = ks_2samp(R, I)
            distribution_ok = D < 0.10 and p > 0.05
        
        iteration += 1
            
        if ((iteration % 5 == 0) and (mask_coverage < target_coverage + 2)):
            min_intervals += 1
        if ((mask_coverage > target_coverage + 2)):
            min_intervals -= 1
    #sample each merged interval and convert samples to strings using index_to_string
    #final_mask = []
    sample_intervals_list = sample_intervals(merged, n=numStringSamples)  # 10 samples per merged interval
    return sample_intervals_list

# ----------------------------------------------STRING--------------------------------------------------------


def create_mask_with_coverage(min_value, max_value, target_coverage, delta):
    if min_value > max_value:
        raise ValueError("min_value must be <= max_value")
    cardinality = max_value - min_value + 1
    band_width = max(1, int(cardinality * delta))  # delta del dominio
    if band_width == 1:
        min_intervals = int(target_coverage / band_width) - 10
    else:
        min_intervals = int((target_coverage / 100) / delta)

    distribution_ok = False
    iteration = 0
    while (
        not distribution_ok or
        (mask_coverage > target_coverage + 2) or
        (mask_coverage < target_coverage - 2)):
        # ---- Generate intervals ----
        intervals = std_generator(min_value, max_value, band_width, min_intervals, cardinality)
        
        # ---- Merge intervals ----
        intervals.sort(key=lambda x: x[0])
        merged = []

        for interval in intervals:
            if not merged:
                merged.append(interval)
            else:
                last_start, last_end = merged[-1]
                curr_start, curr_end = interval

                if curr_start <= last_end:  # overlap
                    merged[-1] = (last_start, max(last_end, curr_end))
                else:
                    merged.append(interval)
        # ---- Calculate mask coverage ----
        mask_coverage = sum(e - s for s,e in merged)/(max_value - min_value)
        mask_coverage = mask_coverage*100

        distribution_ok = kolmogorov_smirnov_test(
            intervals,
            min_value,
            max_value,
            band_width
        )
        
        iteration += 1
            
        if ((iteration % 5 == 0) and (mask_coverage < target_coverage + 2)):
            min_intervals += 1
        if ((mask_coverage > target_coverage + 2)):
            min_intervals -= 1
    # print("Coverage: ", mask_coverage)
    # print("Bands: ", merged)
    return merged
    


def create_mask(min_value, max_value, num_intervals, width):
    """Generate random intervals in [min_value, max_value] allowing
    overflow-wrapping semantics on interval bounds.    """

    if min_value > max_value:
        raise ValueError("min_value must be <= max_value")
    if width < 0:
        raise ValueError("width must be >= 0")

    cardinality = max_value - min_value + 1
    band_width = max(1, int(cardinality * 0.0050))  # 0.12% del dominio

    # ---- Generate intervals ----
    # Use standard generator
    intervals = std_generator(min_value, max_value, width, num_intervals, cardinality)
    # print("Generating ...")
    # ---- Merge intervals ----
    intervals.sort(key=lambda x: x[0])
    merged = []

    for interval in intervals:
        if not merged:
            merged.append(interval)
        else:
            last_start, last_end = merged[-1]
            curr_start, curr_end = interval

            if curr_start <= last_end:  # overlap
                merged[-1] = (last_start, max(last_end, curr_end))
            else:
                merged.append(interval)
    # ---- Calculate mask coverage ----
    mask_coverage = sum(e - s for s,e in merged)/(max_value - min_value)
    # print("Coverage: ", mask_coverage)
   
    # ---- Calculate multiset from intervals ----
    S_real = multiset_from_intervals_2(intervals, min_value, max_value)
    S_ideal = uniform_multiset(min_value, max_value, sum(S_real.values()))


    R = expand_multiset(S_real)
    I = expand_multiset(S_ideal)
    SMALL_SAMPLE_THRESHOLD = 100

    # if band_width == 1:
    #     U, p = mannwhitneyu(R, I, alternative='two-sided')
    # else:
    D_test, p_kstest = kstest(R, 'uniform')
    D_2sample, p_ks2sample = ks_2samp(R, I)

    # ks_stat, ks_pvalue = ks_2samp(R, I)
    # print(f"Uniform multiset: KS stat (D):  {ks_stat:.3f}, P-value: {ks_pvalue}")
    # ks_stat, ks_pvalue = kstest(R, 'uniform')
    # print(f"Uniform distribution: KS stat (D):  {ks_stat:.3f}, P-value: {ks_pvalue}")

    return p_kstest, D_test, p_ks2sample, D_2sample, merged, num_intervals, width, mask_coverage


def select_free_vars(
    free_vars: list[tuple[str, str]],
    keep: list[str] | None = None,
    select_type: str | None = None,
    interactive: bool = True,
) -> list[tuple[str, str]]:
    """
    Select which free variables to keep.
    
    Args:
        free_vars: list of (name, type) tuples
        keep: optional list of variable names to keep directly (skips interaction)
        select_type: if provided, pre-filters free_vars to only variables of this type
        
    Returns:
        list of (name, type) tuples for kept variables
    """
    if select_type is not None:
        free_vars = [(name, typ) for name, typ in free_vars if typ == select_type]

    name_to_var = {name: (name, typ) for name, typ in free_vars}

    # --- Non-interactive mode ---
    if keep is not None or not interactive:
        if keep is None:
            keep = [name for name, _ in free_vars]  # tieni tutto se non specificato
        invalid = [n for n in keep if n not in name_to_var]
        if invalid:
            raise ValueError(f"Unknown variable names: {invalid}")
        selected = [name_to_var[n] for n in keep]
        discarded = [v for v in free_vars if v not in selected]
        print(f"✓ Kept    ({len(selected)}): {[n for n, _ in selected]}")
        print(f"✗ Discarded ({len(discarded)}): {[n for n, _ in discarded]}")
        return selected

    # --- Interactive mode ---
    print("\n=== Free Variable Selection ===")
    type_info = f" of type '{select_type}'" if select_type is not None else ""
    print(f"Found {len(free_vars)} free variables{type_info}:\n")
    for i, (name, typ) in enumerate(free_vars):
        print(f"  [{i}] {name:20s} : {typ}")
    print("\nOptions:")
    print("  - Enter indices to KEEP (e.g. '0 2 3')")
    print("  - Enter 'all' to keep all")
    print("  - Enter 'none' to discard all")
    print("  - Enter variable names directly (e.g. 'call_value1 sender_2')")

    while True:
        choice = input("\nYour selection: ").strip().lower()

        if choice == "all":
            selected = free_vars
            break
        elif choice == "none":
            selected = []
            break
        else:
            tokens = choice.split()
            if all(t.isdigit() for t in tokens):
                indices = [int(t) for t in tokens]
                invalid = [i for i in indices if i >= len(free_vars)]
                if invalid:
                    print(f"  Invalid indices: {invalid}. Try again.")
                    continue
                selected = [free_vars[i] for i in indices]
                break
            invalid = [t for t in tokens if t not in name_to_var]
            if invalid:
                print(f"  Unknown variable names: {invalid}. Try again.")
                continue
            selected = [name_to_var[t] for t in tokens]
            break

    discarded = [v for v in free_vars if v not in selected]
    print(f"\n✓ Kept    ({len(selected)}): {[n for n, _ in selected]}")
    print(f"✗ Discarded ({len(discarded)}): {[n for n, _ in discarded]}")
    return selected
