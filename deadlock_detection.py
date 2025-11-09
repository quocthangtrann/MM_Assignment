"""
deadlock_detection.py

Task 4: Deadlock detection combining ILP + BDD (exact when CandidateBDD enumerable)

"""

from __future__ import annotations
import argparse
import time
import xml.etree.ElementTree as ET
from typing import Dict, Optional, List, Tuple
import pulp

from pnml_parser import PNMLParser, parse_pnml_file, SAMPLE_PNML
from bdd_reachability import BDDReachability

# ------------------------------------------------------------
# Helpers
# ------------------------------------------------------------
def build_dead_bdd_from_petri(bdd_mgr, petri, place_list: List[str]):
    """
    Build BDD (over current vars named exactly as place_list)
    representing dead markings: for every transition t, NOT(enabled_t).
    enabled_t = ∧_{p in pre(t)} var(p)
    """
    mgr = bdd_mgr
    # If any transition has empty pre-set then it's always enabled -> no dead markings at all
    for tid in petri.transitions:
        pre = [arc.source for arc in petri.arcs if arc.source in petri.places and arc.target == tid]
        if len(pre) == 0:
            # a transition with empty pre-set is always enabled => no dead markings
            return mgr.false, False

    dead = mgr.true
    for tid in petri.transitions:
        pre = [arc.source for arc in petri.arcs if arc.source in petri.places and arc.target == tid]
        enabled = mgr.true
        for p in pre:
            enabled &= mgr.var(p)
        dead &= ~enabled
    return dead, True

def marking_from_assignment(assign: Dict[str,bool], place_list: List[str]) -> Dict[str,int]:
    return {p: int(bool(assign.get(p, False))) for p in place_list}

# ILP builder for enumerated candidates:
def solve_selection_ilp(markings: List[Dict[str,int]]) -> Tuple[Optional[Dict[str,int]], str]:
    """
    Given a list of concrete markings (each a dict place->0/1),
    build ILP with binary selection variables y_i, constraint sum y_i == 1,
    optionally link x_p variables to selected marking (x_p = sum_i y_i * m_i[p]).
    Objective: arbitrary (maximize sum x_p) just to give solver an objective.
    Return selected marking if solver finds feasible solution.
    """
    if not markings:
        return None, "No markings provided"

    places = sorted(markings[0].keys())
    n = len(markings)

    prob = pulp.LpProblem("Select_marking_from_candidates", pulp.LpMaximize)

    # selection vars
    y = [pulp.LpVariable(f"y_{i}", cat="Binary") for i in range(n)]
    # optional x vars for places (binary)
    x = {p: pulp.LpVariable(f"x_{p}", cat="Binary") for p in places}

    # pick exactly one marking
    prob += pulp.lpSum(y) == 1

    # link x_p = sum_i y_i * m_i[p]
    for p in places:
        prob += x[p] == pulp.lpSum(y[i] * markings[i][p] for i in range(n))

    # simple objective: maximize sum of x (arbitrary; solver needs objective)
    prob += pulp.lpSum([x[p] for p in places])

    # Solve
    prob.solve(pulp.PULP_CBC_CMD(msg=False, timeLimit=10))
    status = pulp.LpStatus[prob.status] if isinstance(prob.status, int) else prob.status
    if status not in ("Optimal", "Feasible"):
        return None, f"Solver status {status}"

    # find selected index
    sel_idx = None
    for i in range(n):
        val = pulp.value(y[i])
        if val is not None and round(val) == 1:
            sel_idx = i
            break
    if sel_idx is None:
        # fallback: choose first marking
        sel_idx = 0
    return markings[sel_idx], f"OK (status {status})"

# ILP verifier (redundant but uses ILP): enforces marking == sample and checks dead constraints
def verify_dead_with_ilp(petri, marking: Dict[str,int], time_limit: int = 2) -> Tuple[bool, Optional[Dict[str,int]]]:
    places = sorted(petri.places.keys())
    prob = pulp.LpProblem("Verify_dead_marking", pulp.LpStatusOptimal)
    mvars = {p: pulp.LpVariable(f"m_{p}", cat="Binary") for p in places}
    # enforce equality to sampled marking
    for p in places:
        prob += mvars[p] == marking[p]
    # dead constraints: for each transition, sum pre <= |pre|-1
    for tid in petri.transitions:
        pre = [arc.source for arc in petri.arcs if arc.source in petri.places and arc.target == tid]
        if pre:
            prob += pulp.lpSum(mvars[p] for p in pre) <= len(pre) - 1
    prob.solve(pulp.PULP_CBC_CMD(msg=False, timeLimit=time_limit))
    status = pulp.LpStatus[prob.status] if isinstance(prob.status, int) else prob.status
    if status in ("Optimal", "Feasible"):
        # return the marking (should equal input)
        out = {p: int(round(pulp.value(mvars[p]))) for p in places}
        return True, out
    return False, None

# ------------------------------------------------------------
# Main detection function
# ------------------------------------------------------------
def detect_deadlock_ilp_bdd(petri, enum_limit: int = 1000, sample_limit: int = 1000, use_exact_if_small: bool = True):
    """
    Returns one dead marking (dict place->0/1) if found, else None.
    enum_limit: if number of candidates <= enum_limit, enumerate all and run selection ILP.
    sample_limit: if candidate large, sample up to sample_limit candidates and verify by ILP.
    """
    t0_all = time.perf_counter()

    # Build R via BDDReachability
    t0 = time.perf_counter()
    bdd_model = BDDReachability(petri)
    R_bdd, stats = bdd_model.compute_reachability(verbose=False)
    t1 = time.perf_counter()
    time_bdd = t1 - t0

    mgr = bdd_model.bdd
    place_list = bdd_model.place_list

    # Build DeadBDD
    dead_bdd, possible = build_dead_bdd_from_petri(mgr, petri, place_list)
    if not possible:
        print("There exists a transition with empty pre-set (always enabled). No dead markings possible.")
        return None, {"time_bdd": time_bdd, "time_ilp": 0.0, "method": "none (always enabled)"}

    # Candidate = reachable ∧ dead
    candidate = R_bdd & dead_bdd
    if candidate == mgr.false:
        print("No reachable dead markings found (BDD intersection empty).")
        return None, {"time_bdd": time_bdd, "time_ilp": 0.0, "method": "bdd-intersection"}

    # Try to estimate size: attempt to enumerate up to enum_limit+1
    markings = []
    t_enum_start = time.perf_counter()
    count = 0
    try:
        for assign in mgr.sat_iter(candidate):
            markings.append(marking_from_assignment(assign, place_list))
            count += 1
            if count > enum_limit:
                break
    except Exception:
        # If sat_iter fails (unlikely), fallback to sampling
        pass
    t_enum_end = time.perf_counter()
    enum_time = t_enum_end - t_enum_start

    # If enumerated small enough and use_exact_if_small, use ILP selection over enumerated markings
    t_ilp_start = time.perf_counter()
    if use_exact_if_small and 0 < len(markings) <= enum_limit:
        print(f"Candidate dead markings enumerated: {len(markings)} (using ILP selection among them)")
        selected, info = solve_selection_ilp(markings)
        t_ilp_end = time.perf_counter()
        return selected, {"time_bdd": time_bdd, "time_enum": enum_time, "time_ilp": t_ilp_end - t_ilp_start, "method": "enumeration+ilp", "info": info}
    else:
        # Candidate large, fallback to sampling + verify via ILP
        print(f"CandidateBDD large or not fully enumerated; sampled {sample_limit} assignments for ILP verification.")
        sampled = 0
        t_sample_start = time.perf_counter()
        for assign in mgr.pick_iter(candidate):
            if sampled >= sample_limit:
                break
            sampled += 1
            marking = marking_from_assignment(assign, place_list)
            # quick direct check (no ILP) - this is sufficient
            is_dead = True
            for tid in petri.transitions:
                pre = [arc.source for arc in petri.arcs if arc.source in petri.places and arc.target == tid]
                if pre and all(marking.get(p,0) == 1 for p in pre):
                    is_dead = False
                    break
            if is_dead:
                # verify with ILP (time-limited) to conform to assignment
                ok, out = verify_dead_with_ilp(petri, marking, time_limit=2)
                if ok:
                    t_ilp_end = time.perf_counter()
                    return out, {"time_bdd": time_bdd, "time_sample": time.perf_counter()-t_sample_start, "time_ilp": t_ilp_end - t_ilp_start, "method": "sampling+ilp", "sampled": sampled}
        t_sample_end = time.perf_counter()
        t_ilp_end = time.perf_counter()
        return None, {"time_bdd": time_bdd, "time_sample": t_sample_end - t_sample_start, "time_ilp": 0.0, "method": "sampling+ilp", "sampled": sampled}

# ------------------------------------------------------------
# CLI
# ------------------------------------------------------------
def run_cli():
    parser = argparse.ArgumentParser(description="Task 4: Deadlock detection combining ILP + BDD")
    parser.add_argument("file", nargs="?", help="PNML file")
    parser.add_argument("--test", action="store_true", help="Use built-in SAMPLE_PNML")
    parser.add_argument("--enum-limit", type=int, default=1000, help="Max candidates to enumerate for exact ILP")
    parser.add_argument("--sample-limit", type=int, default=1000, help="Max samples to pick when candidate large")
    parser.add_argument("--no-exact", dest="use_exact", action="store_false", help="Don't try exact enumerate+ILP even if small")
    args = parser.parse_args()

    if args.test:
        root = ET.fromstring(SAMPLE_PNML)
        petri = PNMLParser(root).parse()
        print("Using SAMPLE_PNML")
    elif args.file:
        petri = parse_pnml_file(args.file)
    else:
        parser.print_help()
        return

    print(f"Net: {getattr(petri,'id','?')} | Places: {len(petri.places)} | Transitions: {len(petri.transitions)}")
    t0 = time.perf_counter()
    deadmark, stats = detect_deadlock_ilp_bdd(petri, enum_limit=args.enum_limit, sample_limit=args.sample_limit, use_exact_if_small=args.use_exact)
    t1 = time.perf_counter()
    if deadmark:
        print("\nDeadlock (reachable) found:")
        for p, v in deadmark.items():
            print(f"  {p}: {v}")
    else:
        print("\nNo reachable deadlock found (within procedure).")
    print("\nStats:")
    for k, v in stats.items():
        print(f"  {k}: {v}")
    print(f"Total time: {t1 - t0:.4f} s")

if __name__ == "__main__":
    run_cli()
