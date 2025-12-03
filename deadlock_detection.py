"""
deadlock_detection_optimized.py

Task 4: Optimized Deadlock Detection using Hybrid CEGAR approach (ILP + BDD).
Theory based on: Khomenko & Koutny, "Verification of Bounded Petri Nets Using Integer Programming".
"""

from __future__ import annotations
import argparse
import time
import sys
import xml.etree.ElementTree as ET  
from typing import Dict, Optional, List, Tuple, Any

# Check for pulp
try:
    import pulp
except ImportError:
    print("Error: 'pulp' library not found. Install via `pip install pulp`.")
    sys.exit(1)

# Import PNML parser & BDD task
try:
    from pnml_parser import parse_pnml_file, SAMPLE_PNML, PNMLParser
    from bdd_reachability import BDDReachability
except ImportError:
    print("Error: Required modules 'pnml_parser.py' or 'bdd_reachability.py' not found.")
    sys.exit(1)


class ILPDeadlockSolver:
    def __init__(self, petri):
        self.petri = petri
        self.places = sorted(list(petri.places.keys()))
        self.transitions = sorted(list(petri.transitions))
        self.p_idx = {p: i for i, p in enumerate(self.places)}
        self.t_idx = {t: i for i, t in enumerate(self.transitions)}
        
        # Build Incidence Matrix (C)
        # Rows = places, Cols = transitions
        # C[p][t] = W(t, p) - W(p, t)
        self.C = {} # Sparse dict: (place_idx, trans_idx) -> value
        self._build_incidence_matrix()
        
        # Initialize ILP Problem
        self.prob = pulp.LpProblem("Deadlock_Detection_StateEq", pulp.LpMinimize)
        
        # Variables
        # Marking variables m_p (Binary for 1-safe nets)
        self.m_vars = [pulp.LpVariable(f"m_{i}", cat="Binary") for i in range(len(self.places))]
        
        # Firing count variables sigma_t (Integer, non-negative)
        self.sigma_vars = [pulp.LpVariable(f"sigma_{i}", lowBound=0, cat="Integer") for i in range(len(self.transitions))]

        # --- CONSTRAINTS ---
        
        # 1. State Equation: M = M0 + C * sigma
        for i, p in enumerate(self.places):
            m0_val = self.petri.initial_marking.get(p, 0)
            # Gather terms for sum(C[p,t] * sigma[t])
            dot_product_terms = []
            for t_i in range(len(self.transitions)):
                val = self.C.get((i, t_i), 0)
                if val != 0:
                    dot_product_terms.append(val * self.sigma_vars[t_i])
            
            self.prob += (self.m_vars[i] == m0_val + pulp.lpSum(dot_product_terms), f"StateEq_{p}")

        # 2. Deadlock Condition: All transitions must be disabled
        for i, t in enumerate(self.transitions):
            pre_places = self._get_pre_set(t)
            if not pre_places:
                # If a transition has no input places, it is ALWAYS enabled => No Deadlock possible
                # Force infeasibility
                self.prob += (pulp.lpSum([]) == 1, f"Always_Enabled_{t}")
            else:
                # Constraint: sum(m[p] for p in pre(t)) <= len(pre) - 1
                pre_indices = [self.p_idx[p] for p in pre_places if p in self.p_idx]
                self.prob += (pulp.lpSum(self.m_vars[idx] for idx in pre_indices) <= len(pre_indices) - 1, f"Disable_{t}")

    def _build_incidence_matrix(self):
        def get_weight(arc):
            # Handle different ways weight might be stored depending on parser
            val = getattr(arc, 'inscription', 1)
            try:
                return int(val) if val is not None else 1
            except:
                return 1

        # W(p, t): tokens consumed
        for arc in self.petri.arcs:
            if arc.source in self.p_idx and arc.target in self.t_idx:
                p_i = self.p_idx[arc.source]
                t_i = self.t_idx[arc.target]
                w = get_weight(arc)
                self.C[(p_i, t_i)] = self.C.get((p_i, t_i), 0) - w

        # W(t, p): tokens produced
        for arc in self.petri.arcs:
            if arc.source in self.t_idx and arc.target in self.p_idx:
                t_i = self.t_idx[arc.source]
                p_i = self.p_idx[arc.target]
                w = get_weight(arc)
                self.C[(p_i, t_i)] = self.C.get((p_i, t_i), 0) + w

    def _get_pre_set(self, tid):
        return [arc.source for arc in self.petri.arcs 
                if arc.source in self.petri.places and arc.target == tid]

    def add_solution_cut(self, marking: Dict[str, int]):
        """
        Add a constraint to exclude the specific marking found.
        Constraint: Sum(m_p for p where m=0) + Sum(1-m_p for p where m=1) >= 1
        """
        terms = []
        for p, val in marking.items():
            if p not in self.p_idx: continue
            idx = self.p_idx[p]
            if val == 1:
                terms.append(1 - self.m_vars[idx])
            else:
                terms.append(self.m_vars[idx])
        
        self.prob += (pulp.lpSum(terms) >= 1, f"Cut_Solution_{len(self.prob.constraints)}")

    def solve(self) -> Optional[Dict[str, int]]:
        # Use CBC solver, suppress output
        solver = pulp.PULP_CBC_CMD(msg=False, timeLimit=5)
        self.prob.solve(solver)
        
        if self.prob.status == pulp.LpStatusOptimal:
            result = {}
            for i, p in enumerate(self.places):
                val = pulp.value(self.m_vars[i])
                result[p] = int(round(val)) if val is not None else 0
            return result
        return None

def detect_deadlock_optimized(petri):
    print("--- Phase 1: Building Reachability BDD (Oracle) ---")
    bdd_model = BDDReachability(petri)
    R_bdd, stats = bdd_model.compute_reachability(verbose=False)
    print(f"  BDD built in {stats['time_sec']}s. Reachable states: {stats['reachable_count']}")
    
    print("--- Phase 2: Initializing ILP Solver (State Eq + Deadlock) ---")
    ilp_solver = ILPDeadlockSolver(petri)
    
    print("--- Phase 3: CEGAR Loop (ILP Generate -> BDD Verify) ---")
    iteration = 0
    
    while True:
        iteration += 1
        # 1. Solve ILP for a candidate
        candidate = ilp_solver.solve()
        
        if candidate is None:
            print(f"  [Iter {iteration}] ILP Infeasible. No (more) structural deadlocks potential.")
            return None, iteration
            
        # 2. Check with BDD Oracle
        # Check if candidate matches valid place names in BDD
        assignment = {p: bool(v) for p, v in candidate.items() if p in bdd_model.place_set}
        
        # Efficient BDD check: restrict R with assignment. If result is True (1), it's reachable.
        # Note: bdd.let returns a new BDD. If it is not 'false', the assignment is valid.
        # Since we provide full assignment, result should be TRUE or FALSE node.
        check_bdd = bdd_model.bdd.let(assignment, R_bdd)
        is_reachable = (check_bdd == bdd_model.bdd.true)
        
        if is_reachable:
            print(f"  [Iter {iteration}] Candidate Verified! Found Reachable Deadlock.")
            return candidate, iteration
        else:
            # 3. Spurious: Add Cut and Continue
            # print(f"  [Iter {iteration}] Candidate Unreachable (Spurious). Adding cut...")
            ilp_solver.add_solution_cut(candidate)

def run_cli():
    parser = argparse.ArgumentParser(description="Task 4: Optimized Deadlock Detection (CEGAR)")
    parser.add_argument("file", nargs="?", help="PNML file")
    parser.add_argument("--test", action="store_true", help="Use built-in SAMPLE_PNML")
    args = parser.parse_args()

    if args.test:
        if SAMPLE_PNML is None:
            print("Error: SAMPLE_PNML not found in pnml_parser.")
            return
        root = ET.fromstring(SAMPLE_PNML)
        petri = PNMLParser(root).parse()
        print("Using SAMPLE_PNML")
    elif args.file:
        petri = parse_pnml_file(args.file)
    else:
        parser.print_help()
        return

    print(f"Net: {getattr(petri,'id','?')} | Places: {len(petri.places)} | Transitions: {len(petri.transitions)}")
    
    t_start = time.perf_counter()
    deadlock, iters = detect_deadlock_optimized(petri)
    t_end = time.perf_counter()
    
    print("\n" + "="*60)
    if deadlock:
        print(f"RESULT: DEADLOCK FOUND in {t_end - t_start:.4f}s (after {iters} ILP iterations)")
        active_places = [p for p, v in deadlock.items() if v == 1]
        print(f"Deadlock Marking: {active_places}")
    else:
        print(f"RESULT: NO DEADLOCK REACHABLE (Time: {t_end - t_start:.4f}s)")
    print("="*60)

if __name__ == "__main__":
    run_cli()