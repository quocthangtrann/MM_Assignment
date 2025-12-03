#!/usr/bin/env python3
"""
optimization.py
Task 5: Optimization – maximize cᵀM over reachable markings
"""

from __future__ import annotations
import argparse
import time
import sys
import json
from typing import Dict, List, Optional

import xml.etree.ElementTree as ET
from pnml_parser import parse_pnml_file, SAMPLE_PNML, PNMLParser  
from bdd_reachability import BDDReachability


# Check dependencies
try:
    import pulp
except ImportError:
    print("Error: 'pulp' not found. Install with `pip install pulp`.")
    sys.exit(1)

try:
    from pnml_parser import parse_pnml_file, SAMPLE_PNML, PNMLParser
    from bdd_reachability import BDDReachability
    # Re-use solver class from Task 4 if available, or redefine simplified version here
except ImportError:
    print("Error: Required modules not found.")
    sys.exit(1)


class ILPOptimizer:
    def __init__(self, petri, objective_weights: Dict[str, int]):
        self.petri = petri
        self.places = sorted(list(petri.places.keys()))
        self.transitions = sorted(list(petri.transitions))
        self.p_idx = {p: i for i, p in enumerate(self.places)}
        self.t_idx = {t: i for i, t in enumerate(self.transitions)}
        
        # Setup ILP - MAXIMIZE
        self.prob = pulp.LpProblem("Petri_Net_Optimization", pulp.LpMaximize)
        
        # Variables
        self.m_vars = [pulp.LpVariable(f"m_{i}", cat="Binary") for i in range(len(self.places))]
        self.sigma_vars = [pulp.LpVariable(f"sigma_{i}", lowBound=0, cat="Integer") for i in range(len(self.transitions))]

        # 1. Objective Function: Maximize sum(c_p * m_p)
        obj_terms = []
        for p, weight in objective_weights.items():
            if p in self.p_idx:
                obj_terms.append(weight * self.m_vars[self.p_idx[p]])
        self.prob += pulp.lpSum(obj_terms), "Objective_Value"

        # 2. Constraint: State Equation M = M0 + C * sigma
        self._add_state_equation_constraints()

    def _add_state_equation_constraints(self):
        # Build sparse C matrix
        C = {}
        for arc in self.petri.arcs:
            w = int(getattr(arc, 'inscription', 1) or 1)
            if arc.source in self.p_idx and arc.target in self.t_idx: # P->T (consume)
                idx = (self.p_idx[arc.source], self.t_idx[arc.target])
                C[idx] = C.get(idx, 0) - w
            elif arc.source in self.t_idx and arc.target in self.p_idx: # T->P (produce)
                idx = (self.p_idx[arc.target], self.t_idx[arc.source])
                C[idx] = C.get(idx, 0) + w
        
        for i, p in enumerate(self.places):
            m0 = self.petri.initial_marking.get(p, 0)
            dot_prod = []
            for t_j in range(len(self.transitions)):
                val = C.get((i, t_j), 0)
                if val != 0:
                    dot_prod.append(val * self.sigma_vars[t_j])
            # m[p] = m0 + delta
            self.prob += (self.m_vars[i] == m0 + pulp.lpSum(dot_prod), f"StateEq_{p}")

    def solve(self) -> Optional[Dict[str, int]]:
        # Solve using CBC
        solver = pulp.PULP_CBC_CMD(msg=False, timeLimit=10)
        self.prob.solve(solver)
        
        if self.prob.status == pulp.LpStatusOptimal:
            res = {}
            for i, p in enumerate(self.places):
                val = pulp.value(self.m_vars[i])
                res[p] = int(round(val)) if val is not None else 0
            return res
        return None

    def add_cut(self, marking: Dict[str, int]):
        # Cut: Eliminate this specific marking
        # sum(m_i for m=0) + sum(1-m_i for m=1) >= 1
        terms = []
        for p, v in marking.items():
            if p in self.p_idx:
                var = self.m_vars[self.p_idx[p]]
                if v == 1:
                    terms.append(1 - var)
                else:
                    terms.append(var)
        self.prob += (pulp.lpSum(terms) >= 1, f"Cut_Sol_{len(self.prob.constraints)}")


def optimize_cegar(petri, c_weights: Dict[str, int]):
    print(f"\n=== OPTIMIZATION (CEGAR): Maximize Objective ===")
    
    # 1. Build Oracle (BDD)
    t0 = time.perf_counter()
    bdd_model = BDDReachability(petri)
    R_bdd, _ = bdd_model.compute_reachability(verbose=False)
    print(f"  [BDD Oracle] Built in {time.perf_counter() - t0:.4f}s")

    # 2. Setup ILP
    optimizer = ILPOptimizer(petri, c_weights)
    
    # 3. Loop
    iter_count = 0
    while True:
        iter_count += 1
        candidate = optimizer.solve()
        
        if candidate is None:
            print("  [ILP] Infeasible. No reachable markings satisfy constraints.")
            return None, float('-inf'), iter_count
        
        # Calculate objective value for reporting
        obj_val = sum(c_weights.get(p, 0) * candidate.get(p, 0) for p in c_weights)
        
        # Check Reachability
        assign = {p: bool(v) for p, v in candidate.items() if p in bdd_model.place_set}
        is_reachable = (bdd_model.bdd.let(assign, R_bdd) == bdd_model.bdd.true)
        
        if is_reachable:
            print(f"  [Iter {iter_count}] Found VALID Optimal. Value = {obj_val}")
            return candidate, obj_val, iter_count
        else:
            # print(f"  [Iter {iter_count}] Candidate (Val={obj_val}) is Unreachable. Cutting...")
            optimizer.add_cut(candidate)


def run_cli():
    parser = argparse.ArgumentParser()
    parser.add_argument("file", nargs="?", help="PNML file")
    parser.add_argument("--test", action="store_true", help="Use SAMPLE_PNML")
    parser.add_argument("--c", type=str, default="all", help="Objective weights JSON")
    args = parser.parse_args()

    # ... (Parsing logic same as Code 1) ...
    import xml.etree.ElementTree as ET
    if args.test:
        petri = PNMLParser(ET.fromstring(SAMPLE_PNML)).parse()
    elif args.file:
        petri = parse_pnml_file(args.file)
    else:
        return

    # Parse weights
    if args.c == "all":
        # Default: all places have weight 1 (Maximize tokens)
        weights = {p: 1 for p in petri.places}
    else:
        try:
            weights = json.loads(args.c)
        except:
            weights = {p: 1 for p in petri.places}

    t_start = time.perf_counter()
    best_marking, max_val, iters = optimize_cegar(petri, weights)
    t_end = time.perf_counter()
    
    print("\n" + "="*60)
    if best_marking:
        print(f"OPTIMAL VALUE: {max_val}")
        print(f"Time: {t_end - t_start:.4f}s (ILP Iters: {iters})")
        print("Marking:", [p for p, v in best_marking.items() if v==1])
    else:
        print("No solution found.")
    print("="*60)

if __name__ == "__main__":
    run_cli()