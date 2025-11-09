#!/usr/bin/env python3
"""
bdd_reachability.py
Task 3: BDD Symbolic Reachability Analysis for 1-safe Petri Nets
Improved version: interleaved vars, per-rel post-image, XNOR via logical ops,
precomputed presets, safer for medium-sized nets (e.g. 30 places).
"""

from __future__ import annotations
import argparse
import time
import tracemalloc
from typing import Tuple, Dict, Any, Optional, List
from dd import autoref as _bdd
import xml.etree.ElementTree as ET
import json
import sys

# Import parser from Task 1 (must be in same folder)
try:
    from pnml_parser import PNMLParser, parse_pnml_file, SAMPLE_PNML
except Exception as e:
    raise ImportError("pnml_parser.py must be available in the same folder. Error: " + str(e))

# optional explicit BFS import
try:
    from explicit_reachability import explicit_bfs, build_index_maps  # type: ignore
except Exception:
    explicit_bfs = None


class BDDReachability:
    def __init__(self, petri):
        """
        petri: PetriNet object returned by pnml_parser.parse()
        """
        self.petri = petri
        self.bdd = _bdd.BDD()
        self.place_list = sorted(self.petri.places.keys())
        self.n_places = len(self.place_list)

        # variable names for current and next (interleaved declaration helps ordering)
        self.var_current = [f"{p}" for p in self.place_list]
        self.var_next = [f"{p}'" for p in self.place_list]

        # declare variables in interleaved order: p, p', q, q', ...
        for p in self.place_list:
            self.bdd.add_var(p)
            self.bdd.add_var(f"{p}'")

        # precompute pre/post sets for transitions to avoid recomputations
        self.pre_sets: Dict[str, List[str]] = {}
        self.post_sets: Dict[str, List[str]] = {}
        self._compute_pre_post_sets()

        # build per-transition relations (no global rel_total to avoid huge OR)
        self.transitions_rel = []
        self._build_transition_relations()

    def _compute_pre_post_sets(self):
        arcs = self.petri.arcs
        places = self.petri.places
        transitions = self.petri.transitions
        for tid in sorted(transitions.keys()):
            pre = [arc.source for arc in arcs if arc.source in places and arc.target == tid]
            post = [arc.target for arc in arcs if arc.source == tid and arc.target in places]
            self.pre_sets[tid] = pre
            self.post_sets[tid] = post

    # ---------------------------
    # Internal builders
    # ---------------------------
    def _build_transition_relations(self):
        """
        Build transition relation BDDs.
        Each relation rel is a BDD over vars {current_vars, next_vars} representing:
            enabled(current) & update(current,next)
        where:
            - enabled(current): all pre places == 1
            - update: pre places -> 0, post places -> 1, others unchanged (equivalence)
        Note: we DO NOT build a single rel_total by OR-ing all rels to avoid blow-up.
        """
        arcs = self.petri.arcs
        transitions = self.petri.transitions
        places = self.petri.places

        for tid in sorted(transitions.keys()):
            pre = set(self.pre_sets.get(tid, []))
            post = set(self.post_sets.get(tid, []))

            # verify weights (inscription)
            for arc in arcs:
                if arc.source in places and arc.target == tid:
                    weight = getattr(arc, "inscription", 1)
                    if weight != 1:
                        raise ValueError(f"Arc {arc.id}: weight={weight} ≠ 1. This tool assumes 1-safe nets and weight=1.")

            # enabled: conjunction of current vars for pre places
            enabled = self.bdd.true
            for p in pre:
                enabled &= self.bdd.var(p)

            # update: pre -> 0, post -> 1, others: equivalence x == x'
            update = self.bdd.true
            for p in pre:
                update &= ~self.bdd.var(f"{p}'")
            for p in post:
                update &= self.bdd.var(f"{p}'")
            others = set(self.place_list) - pre - post
            for p in others:
                xp = self.bdd.var(p)
                xnp = self.bdd.var(f"{p}'")
                # equivalence: x == x'  <=>  (x & x') | (~x & ~x')
                update &= (xp & xnp) | (~xp & ~xnp)

            rel = enabled & update
            self.transitions_rel.append(rel)

        # Do not create combined rel_total to avoid giant OR operations
        self._rel_total = None

    # ---------------------------
    # Initial states
    # ---------------------------
    def initial_bdd(self):
        """Return BDD representing initial marking."""
        f = self.bdd.true
        # Places not in initial_marking are considered 0 by default
        for p in self.place_list:
            tokens = self.petri.initial_marking.get(p, 0)
            if tokens == 1:
                f &= self.bdd.var(p)
            elif tokens == 0:
                f &= ~self.bdd.var(p)
            else:
                raise ValueError(f"Initial marking not 1-safe: place {p} has {tokens} tokens.")
        return f

    # ---------------------------
    # Post-image computation
    # ---------------------------
    def post_image(self, R):
        """
        Compute post-image by existentially quantifying current vars on each transition relation,
        then OR the results. Safer than combining all relations into one big BDD.
        """
        if not self.transitions_rel:
            return self.bdd.false

        next_states = self.bdd.false
        # iterate per-rel to avoid building one enormous BDD
        for rel in self.transitions_rel:
            # R & rel is over current + next vars; exist current vars -> function over next vars
            product = R & rel
            img = self.bdd.exist(self.var_current, product)
            next_states |= img

        # rename next -> current using manager.let(mapping, function)
        rename_map = {f"{p}'": p for p in self.place_list}
        return self.bdd.let(rename_map, next_states)

    # ---------------------------
    # Reachability fixpoint
    # ---------------------------
    def compute_reachability(self, verbose: bool = False, max_steps: Optional[int] = None) -> Tuple[Any, Dict[str, Any]]:
        """
        Compute fixpoint R := R ∪ post(R) until stable.
        Returns (R_bdd, stats_dict)
        """
        tracemalloc.start()
        t0 = time.perf_counter()

        R = self.initial_bdd()
        steps = 0
        prev_count = -1

        # If verbose, print initial info
        if verbose:
            print(f"Initial BDD built. Starting fixpoint iteration...")

        while True:
            steps += 1
            # compute post
            newR = R | self.post_image(R)

            # If verbose, attempt to count (may be expensive)
            new_count = -1
            if verbose:
                try:
                    new_count = int(self.bdd.count(newR))
                except Exception:
                    new_count = -1

            if newR == R:
                if verbose:
                    print(f"Converged at step {steps}.")
                break

            R = newR
            if verbose:
                if new_count >= 0:
                    delta = new_count - prev_count if prev_count >= 0 else new_count
                    print(f"  Step {steps}: count={new_count} (+{delta})")
                else:
                    print(f"  Step {steps}: (count unknown)")
            prev_count = new_count

            if max_steps is not None and steps >= max_steps:
                if verbose:
                    print(f"Reached max_steps={max_steps}; stopping iteration early.")
                break

        t1 = time.perf_counter()
        current, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()

        # Try to get node count for BDD representing R
        bdd_node_count: Optional[int] = None
        try:
            if hasattr(self.bdd, "dag_size"):
                bdd_node_count = int(self.bdd.dag_size(R))
            elif hasattr(self.bdd, "count_nodes"):
                bdd_node_count = int(self.bdd.count_nodes(R))
            else:
                bdd_node_count = int(len(self.bdd))
        except Exception:
            bdd_node_count = None

        # reachable count (attempt)
        reachable_count: Optional[int] = None
        try:
            reachable_count = int(self.bdd.count(R))
        except Exception:
            reachable_count = None

        stats = {
            "method": "BDD",
            "steps": steps,
            "time_sec": t1 - t0,
            "peak_memory_kb": peak / 1024.0,
            "reachable_count": reachable_count,
            "bdd_node_count": bdd_node_count,
        }
        return R, stats


# ---------------------------
# optional explicit comparison utilities
# ---------------------------
def run_explicit_and_compare(petri, limit: int = 0) -> Dict[str, Any]:
    """
    Run explicit BFS (if available) to gather stats for comparison.
    Returns dict with time, peak_memory_kb, reachable_count.
    """
    if explicit_bfs is None:
        raise ImportError("explicit_reachability.py not available (explicit_bfs import failed).")
    tracemalloc.start()
    t0 = time.perf_counter()
    reachable_masks, _ = explicit_bfs(petri, limit=limit)
    t1 = time.perf_counter()
    current, peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()

    return {
        "method": "Explicit BFS",
        "time_sec": t1 - t0,
        "peak_memory_kb": peak / 1024.0,
        "reachable_count": len(reachable_masks)
    }


# ---------------------------
# CLI and printing
# ---------------------------
def print_stats(stats: Dict[str, Any], prefix: str = ""):
    print(f"{prefix}Method: {stats.get('method','?')}")
    if "time_sec" in stats and stats["time_sec"] is not None:
        print(f"{prefix}  Time: {stats['time_sec']:.4f} s")
    if "peak_memory_kb" in stats and stats["peak_memory_kb"] is not None:
        print(f"{prefix}  Peak memory: {stats['peak_memory_kb']:.1f} KiB")
    if "reachable_count" in stats:
        print(f"{prefix}  Reachable markings: {stats['reachable_count']}")
    if "steps" in stats:
        print(f"{prefix}  Fixpoint steps: {stats['steps']}")
    if "bdd_node_count" in stats:
        print(f"{prefix}  BDD nodes: {stats['bdd_node_count']}")


def run_cli():
    parser = argparse.ArgumentParser(description="Task 3: BDD Symbolic Reachability (improved)")
    parser.add_argument("file", nargs="?", help="PNML file path")
    parser.add_argument("--test", action="store_true", help="Use built-in SAMPLE_PNML")
    parser.add_argument("--stats", action="store_true", help="Verbose iteration stats")
    parser.add_argument("--compare", action="store_true", help="Run explicit BFS (if available) and compare stats")
    parser.add_argument("--max-steps", type=int, default=0, help="Maximum fixpoint iterations (0 = unlimited)")
    args = parser.parse_args()

    # load Petri net
    if args.test:
        root = ET.fromstring(SAMPLE_PNML)
        petri = PNMLParser(root).parse()
        print("Using built-in SAMPLE_PNML")
    elif args.file:
        petri = parse_pnml_file(args.file)
    else:
        parser.print_help()
        return

    print(f"Net: {petri.id or 'unknown'} | Places: {len(petri.places)} | Transitions: {len(petri.transitions)}")

    # run BDD reachability
    bdd_model = BDDReachability(petri)
    max_steps = args.max_steps if args.max_steps > 0 else None
    R_bdd, bdd_stats = bdd_model.compute_reachability(verbose=args.stats, max_steps=max_steps)
    print_stats(bdd_stats, prefix="BDD │ ")

    # optional comparison with explicit BFS
    if args.compare:
        if explicit_bfs is None:
            print("Explicit BFS not available (explicit_reachability.py missing). Cannot compare.")
        else:
            try:
                exp_stats = run_explicit_and_compare(petri)
                print()
                print_stats(exp_stats, prefix="EXP │ ")
                # comparative metrics if both times available and non-zero
                try:
                    speedup = exp_stats["time_sec"] / bdd_stats["time_sec"] if bdd_stats["time_sec"] > 0 else None
                    mem_ratio = exp_stats["peak_memory_kb"] / bdd_stats["peak_memory_kb"] if bdd_stats["peak_memory_kb"] > 0 else None
                    if speedup is not None:
                        print(f"\nComparison:")
                        if speedup is not None:
                            print(f"  Speedup (explicit / bdd): {speedup:.2f}x")
                        if mem_ratio is not None:
                            print(f"  Memory ratio (explicit / bdd): {mem_ratio:.2f}x")
                except Exception:
                    pass
            except Exception as e:
                print("Comparison failed:", e)

    else:
        if explicit_bfs is not None:
            print("\nTip: run with `--compare` to run and compare explicit BFS (if explicit_reachability.py is present).")


if __name__ == "__main__":
    run_cli()
