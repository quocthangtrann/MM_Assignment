#!/usr/bin/env python3
"""
bdd_reachability.py

Task 3: Symbolic Reachability for 1-safe Petri Nets using BDD.

Features:
- Parse Petri net object (expects pnml_parser.parse_pnml_file or PNMLParser to exist)
- Build BDD variables for places and prime variables for next-state
- Build transition relations WITH frame condition (no early existential quantification)
- Compute post-image: product = R & rel -> exist(current_vars, product) -> rename primes -> current
- Compute least fixpoint R = R | Post(R)
- Report timing / peak memory / BDD node count (dag_size) / reachable count
- Optional compare with explicit BFS (if explicit_reachability.explicit_bfs available)
- Optional dump of all reachable markings
"""

from __future__ import annotations
import argparse
import time
import tracemalloc
from typing import Tuple, Dict, Any, List, Set
import xml.etree.ElementTree as ET
import sys

# BDD library
try:
    from dd import autoref as _bdd
except Exception as e:
    print("Error importing dd.autoref (python-dd). Install with `pip install dd`.")
    raise

# Try import PNML parser & explicit reachability (user must provide these modules)
try:
    from pnml_parser import parse_pnml_file, SAMPLE_PNML, PNMLParser  # type: ignore
except Exception:
    parse_pnml_file = None
    PNMLParser = None
    SAMPLE_PNML = None

try:
    from explicit_reachability import explicit_bfs  # type: ignore
except Exception:
    explicit_bfs = None


class BDDReachability:
    def __init__(self, petri):
        """
        petri: an object returned by pnml_parser.parse_pnml_file or PNMLParser.parse()
               Expected attributes:
                 - places: dict(place_id -> place_obj)
                 - transitions: iterable of transition ids
                 - arcs: iterable of arc objs with at least: source, target, maybe inscription/weight
                 - initial_marking: dict(place_id -> 0/1)
                 - id (optional)
        """
        self.petri = petri
        self.bdd = _bdd.BDD()
        # get place ids and labels (use name if present)
        place_ids = list(self.petri.places.keys())
        labels: List[str] = []
        for pid in place_ids:
            name = getattr(self.petri.places[pid], "name", None)
            labels.append(name.strip() if (name and isinstance(name, str) and name.strip()) else pid)

        # Heuristic ordering (can improve BDD size)
        self.place_list = self._heuristic_ordering(place_ids, labels)

        # create variables p and p' (prime)
        for p in self.place_list:
            # add current var
            self.bdd.add_var(p)
            # add prime var
            self.bdd.add_var(f"{p}'")

        # list of current variable names for exist quantification
        self.var_current = self.place_list[:]  # names (strings)
        # also create a set for quick membership
        self.place_set: Set[str] = set(self.place_list)

        # pre/post sets
        self.pre_sets = {}
        self.post_sets = {}
        self._compute_pre_post_sets()

        # build transition relations (no early quantification)
        self.transitions_rel = []
        self._build_transition_relations()

    def _heuristic_ordering(self, place_ids: List[str], labels: List[str]) -> List[str]:
        # basic heuristic: if small, keep natural order
        if len(place_ids) <= 20:
            return place_ids[:]

        ordered: List[str] = []
        seen: Set[str] = set()

        # group by numbers appearing in labels (1..N)
        for i in range(1, 500):
            group = [pid for pid, lab in zip(place_ids, labels) if lab and str(i) in lab and pid not in seen]
            if group:
                group.sort(key=lambda x: labels[place_ids.index(x)])
                ordered.extend(group)
                seen.update(group)

        # common prefixes
        prefixes = ['FORK', 'EAT', 'THINK', 'WAIT', 'IDLE', 'CRITICAL', 'CS', 'BUF', 'BUFFER',
                    'READ', 'WRITE', 'PROD', 'CONS', 'TOKEN', 'LOCK', 'MUTEX', 'ENTRY', 'EXIT', 'P']
        for pref in prefixes:
            group = [pid for pid, lab in zip(place_ids, labels) if lab and lab.startswith(pref) and pid not in seen]
            if len(group) >= 2:
                ordered.extend(group)
                seen.update(group)

        # remaining
        remaining = [pid for pid in place_ids if pid not in seen]
        remaining.sort(key=lambda x: (labels[place_ids.index(x)] or x))
        ordered.extend(remaining)
        return ordered

    def _compute_pre_post_sets(self):
        places = set(self.petri.places.keys())
        for tid in self.petri.transitions:
            pre = [a.source for a in self.petri.arcs if a.source in places and a.target == tid]
            post = [a.target for a in self.petri.arcs if a.source == tid and a.target in places]
            self.pre_sets[tid] = pre
            self.post_sets[tid] = post

    def _arc_weight(self, arc):
        # try a few attribute names
        for attr in ("inscription", "weight", "text", "multiplicity"):
            if hasattr(arc, attr):
                try:
                    val = getattr(arc, attr)
                    # sometimes inscription may be an object or XML element; handle common types
                    if isinstance(val, str):
                        return int(val)
                    try:
                        return int(val)
                    except Exception:
                        pass
                except Exception:
                    pass
        # default
        return 1

    def _build_transition_relations(self):
        """
        Build transition relations keeping both current and prime variables.
        Do NOT existentially quantify current vars here. Quantify only AFTER multiplying with R.
        Include frame condition for unchanged places: p' == p
        """
        self.transitions_rel = []
        all_places = set(self.place_list)

        # validate weights = 1 for arcs connecting place <-> transition
        for arc in self.petri.arcs:
            if arc.source in self.petri.places and arc.target in self.petri.transitions:
                w = self._arc_weight(arc)
                if w != 1:
                    raise ValueError(f"Unsupported arc weight {w} from place {arc.source} to transition {arc.target}")
            if arc.target in self.petri.places and arc.source in self.petri.transitions:
                w = self._arc_weight(arc)
                if w != 1:
                    raise ValueError(f"Unsupported arc weight {w} from transition {arc.source} to place {arc.target}")

        for tid in self.petri.transitions:
            pre = set(self.pre_sets.get(tid, []))
            post = set(self.post_sets.get(tid, []))

            # enabled(current) = ∧_{p ∈ pre} p
            enabled = self.bdd.true
            for p in pre:
                # if p is not in place_list (maybe PNML uses different ids) skip gracefully
                if p not in self.place_set:
                    continue
                enabled &= self.bdd.var(p)

            # next-state constraints over prime vars
            next_state = self.bdd.true
            # p removed (pre \ post) -> p' = 0
            for p in pre - post:
                if p not in self.place_set:
                    continue
                next_state &= ~self.bdd.var(f"{p}'")
            # p added (post \ pre) -> p' = 1
            for p in post - pre:
                if p not in self.place_set:
                    continue
                next_state &= self.bdd.var(f"{p}'")
            # p preserved (pre & post) -> p' = 1
            for p in pre & post:
                if p not in self.place_set:
                    continue
                next_state &= self.bdd.var(f"{p}'")

            # frame condition for unchanged places: p' == p
            for p in (all_places - pre - post):
                xp = self.bdd.var(p)
                xnp = self.bdd.var(f"{p}'")
                # (xp & xnp) | (~xp & ~xnp)
                next_state &= (xp & xnp) | (~xp & ~xnp)

            Ti = enabled & next_state
            self.transitions_rel.append(Ti)

    def initial_bdd(self):
        f = self.bdd.true
        for p in self.place_list:
            tokens = self.petri.initial_marking.get(p, 0)
            if tokens == 1:
                f &= self.bdd.var(p)
            elif tokens == 0:
                f &= ~self.bdd.var(p)
            else:
                raise ValueError(f"Place {p} has {tokens} tokens – only 1-safe nets supported")
        return f

    def post_image(self, R):
        """Compute Post(R) = { s' | exists s in R and t: (s,t,s') }.
        Implemented as: for each transition rel:
            product = R(current) & rel(current, prime)
            img = exist(current_vars, product)  # img over prime vars only
            next_states |= img
        finally rename prime -> current
        """
        if not self.transitions_rel:
            return self.bdd.false

        next_states = self.bdd.false
        for rel in self.transitions_rel:
            product = R & rel
            # existentially quantify current variables (var_current is list of current var names)
            img = self.bdd.exist(self.var_current, product)
            next_states |= img

        # rename prime vars p' -> p, to express next_states over current vars
        rename_map = {f"{p}'": p for p in self.place_list}
        return self.bdd.let(rename_map, next_states)

    def compute_reachability(self, verbose: bool = False) -> Tuple[Any, Dict[str, Any]]:
        tracemalloc.start()
        t0 = time.perf_counter()

        R = self.initial_bdd()
        steps = 0

        # fixpoint loop
        while True:
            steps += 1
            newR = R | self.post_image(R)
            if newR == R:
                break
            R = newR
            if verbose:
                try:
                    size = self.bdd.dag_size(R)
                except Exception:
                    size = None
                print(f"[debug] step {steps}: dag_size(R)={size}")

        t1 = time.perf_counter()
        _, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()

        # BDD node count for R
        try:
            node_count = self.bdd.dag_size(R)
        except Exception:
            node_count = len(self.bdd)

        # ensure R has only current variables (we rename p'->p in post_image)
        try:
            state_count = int(self.bdd.count(R))
        except Exception:
            # fallback: approximate or mark unknown
            state_count = -1

        stats = {
            "method": "BDD (frame condition, heuristic ordering)",
            "time_sec": round(t1 - t0, 4),
            "peak_memory_kb": round(peak / 1024, 1),
            "reachable_count": state_count,
            "bdd_node_count": node_count,
            "steps": steps
        }
        return R, stats


# ===== CLI & helpers =====
def print_stats(stats: Dict[str, Any], prefix: str = ""):
    print(f"{prefix}Method: {stats.get('method','?')}")
    print(f"{prefix}  Time: {stats.get('time_sec',0):.4f} s")
    print(f"{prefix}  Peak memory: {stats.get('peak_memory_kb',0):.1f} KiB")
    print(f"{prefix}  Reachable markings: {stats.get('reachable_count')}")
    if 'bdd_node_count' in stats:
        print(f"{prefix}  BDD nodes: {stats.get('bdd_node_count')}")
    if 'steps' in stats:
        print(f"{prefix}  Fixpoint steps: {stats.get('steps')}")


def run_cli():
    parser = argparse.ArgumentParser(description="Task 3: BDD Reachability (1-safe Petri nets)")
    parser.add_argument("file", nargs="?", help="File PNML")
    parser.add_argument("--test", action="store_true", help="Use SAMPLE_PNML if available")
    parser.add_argument("--compare", action="store_true", help="Compare with explicit BFS (if available)")
    parser.add_argument("--dump", action="store_true", help="Dump all reachable markings (may be large)")
    parser.add_argument("--verbose", action="store_true", help="Verbose debug output")
    args = parser.parse_args()

    if args.test:
        if PNMLParser is None or SAMPLE_PNML is None:
            print("No SAMPLE_PNML / PNMLParser available in pnml_parser.py.")
            return
        petri = PNMLParser(ET.fromstring(SAMPLE_PNML)).parse()
    elif args.file:
        if parse_pnml_file is None:
            print("pnml_parser.parse_pnml_file not available. Put pnml_parser.py in same folder.")
            return
        petri = parse_pnml_file(args.file)
    else:
        parser.print_help()
        return

    net_name = getattr(petri, 'id', None) or 'unknown'
    print(f"Net: {net_name} | Places: {len(petri.places)} | Transitions: {len(petri.transitions)}\n")

    model = BDDReachability(petri)
    R, bdd_stats = model.compute_reachability(verbose=args.verbose)
    print_stats(bdd_stats, "BDD │ ")

    # Compare with explicit BFS if requested and available
    if args.compare:
        if explicit_bfs is None:
            print("\n[WARN] explicit_bfs not available (explicit_reachability.py missing). Skipping compare.")
        else:
            tracemalloc.start()
            t0 = time.perf_counter()
            masks, _info = explicit_bfs(petri)
            t1 = time.perf_counter()
            _, peak = tracemalloc.get_traced_memory()
            tracemalloc.stop()

            exp_stats = {
                "method": "Explicit BFS",
                "time_sec": round(t1 - t0, 4),
                "peak_memory_kb": round(peak / 1024, 1),
                "reachable_count": len(masks)
            }
            print("\n" + "-" * 60)
            print_stats(exp_stats, "EXP │ ")

    # Dump (iterate assignments)
    if args.dump:
        rc = bdd_stats.get('reachable_count', None)
        print(f"\n{'='*60}")
        print(f" DUMPING ALL {rc if rc is not None else '?'} REACHABLE MARKINGS ")
        print(f"{'='*60}")
        count = 0
        try:
            for assignment in model.bdd.pick_iter(R):
                count += 1
                active = [p for p in model.place_list if assignment.get(p, False)]
                print(f"{count:6d}: {', '.join(active) if active else 'EMPTY'}")
        except Exception as e:
            print(f"[ERROR] while dumping: {e}")
        print(f"\n→ Finished printing {count} marking(s).\n")


if __name__ == "__main__":
    run_cli()
