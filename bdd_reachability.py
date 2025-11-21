"""
bdd_reachability.py
Task 3: Symbolic Reachability and BDD for 1-safe Petri Nets
"""

from __future__ import annotations
import argparse
import time
import tracemalloc
from typing import Tuple, Dict, Any, Optional, List
from dd import autoref as _bdd
import xml.etree.ElementTree as ET
import sys

# Import parser và explicit
try:
    from pnml_parser import parse_pnml_file, SAMPLE_PNML, PNMLParser
except ImportError:
    raise ImportError("pnml_parser.py phải cùng thư mục")

try:
    from explicit_reachability import explicit_bfs
except ImportError:
    explicit_bfs = None


class BDDReachability:
    def __init__(self, petri):
        self.petri = petri
        self.bdd = _bdd.BDD()


        place_ids = list(self.petri.places.keys())
        labels = []
        for pid in place_ids:
            name = getattr(self.petri.places[pid], "name", None)
            labels.append(name.strip() if name and name.strip() else pid)

        self.place_list = self._heuristic_ordering(place_ids, labels)

        for p in self.place_list:
            self.bdd.add_var(p)
            self.bdd.add_var(f"{p}'")

        self.var_current = self.place_list[:]

        # Precompute pre/post sets
        self.pre_sets = {}
        self.post_sets = {}
        self._compute_pre_post_sets()

        # Build transition relations
        self.transitions_rel = []
        self._build_transition_relations()

    def _heuristic_ordering(self, place_ids: List[str], labels: List[str]) -> List[str]:
        if len(place_ids) <= 20:
            return place_ids

        ordered = []
        seen = set()

        # 1. Group number
        for i in range(1, 200):
            group = [pid for pid, lab in zip(place_ids, labels) if str(i) in lab and pid not in seen]
            if group:
                group.sort(key=lambda x: labels[place_ids.index(x)])  # sort theo name
                ordered.extend(group)
                seen.update(group)

        # 2. Group popular prefix
        prefixes = ['FORK','EAT','THINK','WAIT','IDLE','CRITICAL','CS','BUF','BUFFER',
                    'READ','WRITE','PROD','CONS','TOKEN','LOCK','MUTEX','ENTRY','EXIT','P']
        for pref in prefixes:
            group = [pid for pid, lab in zip(place_ids, labels) if lab.startswith(pref) and pid not in seen]
            if len(group) >= 2:
                ordered.extend(group)
                seen.update(group)

        # 3. Remaining – sort 
        remaining = [pid for pid in place_ids if pid not in seen]
        remaining.sort(key=lambda x: labels[place_ids.index(x)] or x)
        ordered.extend(remaining)

        return ordered

    def _compute_pre_post_sets(self):
        places_set = set(self.petri.places.keys())
        for tid in self.petri.transitions:
            pre = [a.source for a in self.petri.arcs if a.source in places_set and a.target == tid]
            post = [a.target for a in self.petri.arcs if a.source == tid and a.target in places_set]
            self.pre_sets[tid] = pre
            self.post_sets[tid] = post

    def _build_transition_relations(self):
        for tid in self.petri.transitions:
            pre = set(self.pre_sets.get(tid, []))
            post = set(self.post_sets.get(tid, []))

            # Check weight = 1
            for arc in self.petri.arcs:
                if arc.source in self.petri.places and arc.target == tid and getattr(arc, "inscription", 1) != 1:
                    raise ValueError("Weight != 1 – only 1-safe nets supported")

            enabled = self.bdd.true
            for p in pre:
                enabled &= self.bdd.var(p)

            update = self.bdd.true
            for p in pre:
                update &= ~self.bdd.var(f"{p}'")
            for p in post:
                update &= self.bdd.var(f"{p}'")
            for p in set(self.place_list) - pre - post:
                xp = self.bdd.var(p)
                xnp = self.bdd.var(f"{p}'")
                update &= (xp & xnp) | (~xp & ~xnp)

            self.transitions_rel.append(enabled & update)

    def initial_bdd(self):
        f = self.bdd.true
        for p in self.place_list:
            tokens = self.petri.initial_marking.get(p, 0)
            if tokens == 1:
                f &= self.bdd.var(p)
            elif tokens == 0:
                f &= ~self.bdd.var(p)
            else:
                raise ValueError(f"Place {p} has {tokens} tokens")
        return f

    def post_image(self, R):
        if not self.transitions_rel:
            return self.bdd.false

        next_states = self.bdd.false
        for rel in self.transitions_rel:
            product = R & rel
            img = self.bdd.exist(self.var_current, product)
            next_states |= img

        rename_map = {f"{p}'": p for p in self.place_list}
        return self.bdd.let(rename_map, next_states)

    def compute_reachability(self, verbose=False) -> Tuple[Any, Dict]:
        tracemalloc.start()
        t0 = time.perf_counter()

        R = self.initial_bdd()
        steps = 0

        while True:
            steps += 1
            newR = R | self.post_image(R)
            if newR == R:
                break
            R = newR

        t1 = time.perf_counter()
        _, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()

        try:
            node_count = self.bdd.dag_size(R)
        except:
            node_count = len(self.bdd)

        state_count = int(self.bdd.count(R))

        stats = {
            "method": "BDD (smart ordering + place.name)",
            "time_sec": round(t1 - t0, 4),
            "peak_memory_kb": round(peak / 1024, 1),
            "reachable_count": state_count,
            "bdd_node_count": node_count,
            "steps": steps
        }
        return R, stats
    

# ==================== CLI + COMPARE ====================
def print_stats(stats: Dict, prefix=""):
    print(f"{prefix}Method: {stats['method']}")
    print(f"{prefix}  Time: {stats['time_sec']:.4f} s")
    print(f"{prefix}  Peak memory: {stats['peak_memory_kb']:.1f} KiB")
    print(f"{prefix}  Reachable markings: {stats['reachable_count']}")
    if 'bdd_node_count' in stats:
        print(f"{prefix}  BDD nodes: {stats['bdd_node_count']}")
    if 'steps' in stats:
        print(f"{prefix}  Fixpoint steps: {stats['steps']}")

def run_cli():
    parser = argparse.ArgumentParser(description="Task 3: BDD Reachability")
    parser.add_argument("file", nargs="?", help="File PNML")
    parser.add_argument("--test", action="store_true", help="Dùng SAMPLE_PNML")
    parser.add_argument("--compare", action="store_true", help="compare with explicit BFS")
    parser.add_argument("--dump", action="store_true", help="In toàn bộ reachable markings")
    args = parser.parse_args()

    if args.test:
        petri = PNMLParser(ET.fromstring(SAMPLE_PNML)).parse()
    elif args.file:
        petri = parse_pnml_file(args.file)
    else:
        parser.print_help()
        return

    print(f"Net: {petri.id or 'unknown'} | Places: {len(petri.places)} | Transitions: {len(petri.transitions)}\n")

    model = BDDReachability(petri)
    R, bdd_stats = model.compute_reachability()
    print_stats(bdd_stats, "BDD │ ")

    if args.compare and explicit_bfs is not None:
        tracemalloc.start()
        t0 = time.perf_counter()
        masks, _ = explicit_bfs(petri)
        t1 = time.perf_counter()
        _, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()

        exp_stats = {
            "method": "Explicit BFS",
            "time_sec": round(t1 - t0, 4),
            "peak_memory_kb": round(peak / 1024, 1),
            "reachable_count": len(masks)
        }
        print()
        print_stats(exp_stats, "EXP │ ")
        

    if args.dump:
        print(f"\n{'='*20} DUMPING ALL {bdd_stats['reachable_count']} REACHABLE MARKINGS {'='*20}")
        count = 0
        for assignment in model.bdd.pick_iter(R):
            count += 1
            active_places = [p for p in model.place_list if assignment.get(p, False)]
            print(f"{count:4d}: {', '.join(active_places) if active_places else 'EMPTY'}")
        print(f"\n→ finish printing {count} marking(s).\n")

if __name__ == "__main__":
    run_cli()