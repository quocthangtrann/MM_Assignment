#!/usr/bin/env python3
"""
optimization.py
Task 5: Optimization – maximize cᵀM over reachable markings
"""

from __future__ import annotations
import argparse
import time
import json
from typing import Dict, List

import xml.etree.ElementTree as ET
from pnml_parser import parse_pnml_file, SAMPLE_PNML, PNMLParser  # <--- SỬA: thêm PNMLParser
from bdd_reachability import BDDReachability


def optimize_reachable(
    petri,
    c: Dict[str, int],
    place_list: List[str],
    R,
    bdd_mgr,
    bdd_stats: Dict,  
    total_start_time: float,  
) -> None:
    print("\n=== TASK 5: OPTIMIZATION max cᵀM over Reach(M₀) ===")
    
    if not c:
        print("No objective coefficients provided – using c_p = 1 for all places")
        c = {p: 1 for p in place_list}
    
    t0 = time.perf_counter()
    
    max_value = float('-inf')
    best_marking: Dict[str, int] = {}
    
    reachable_count = 0
    for assignment in bdd_mgr.pick_iter(R):
        reachable_count += 1
        current_value = sum(c.get(p, 0) * (1 if assignment.get(p, False) else 0) for p in place_list)
        
        if current_value > max_value:
            max_value = current_value
            best_marking = {p: 1 for p in place_list if assignment.get(p, False)}
    
    t1 = time.perf_counter()
    
    if reachable_count == 0:
        print("No reachable markings found (impossible case)")
        return
    
    print(f"Optimal value (max cᵀM): {max_value}")
    print(f"Found in {t1 - t0:.4f} seconds after enumerating {reachable_count} reachable markings")
    print("One optimal marking (places with token = 1):")
    if best_marking:
        for p in sorted(best_marking.keys()):
            print(f"  {p}: 1")
    else:
        print("  EMPTY marking (all places = 0)")

    # SỬA LỖI DÒNG PRINT CUỐI (bỏ lặp và dùng total_start_time)
    print(f"\n→ Total time (including BDD reachability): {t1 - total_start_time:.4f} s")


def run_cli():
    parser = argparse.ArgumentParser(description="Task 5: Optimization over reachable markings")
    parser.add_argument("file", nargs="?", help="PNML file (required unless --test)")
    parser.add_argument("--test", action="store_true", help="Use built-in SAMPLE_PNML")
    parser.add_argument("--c", type=str, default="all", 
                        help="Objective vector c as JSON dict or 'all' (default: all)")
    args = parser.parse_args()

    if args.test:
        root = ET.fromstring(SAMPLE_PNML)
        petri = PNMLParser(root).parse()
    elif args.file:
        petri = parse_pnml_file(args.file)
    else:
        parser.print_help()
        return

    # Tính reachable BDD
    model = BDDReachability(petri)
    t_start = time.perf_counter()  # <--- sửa tên biến cho rõ
    R, bdd_stats = model.compute_reachability()
    
    # Parse c
    if args.c == "all":
        c_dict = {p: 1 for p in model.place_list}
    else:
        try:
            c_dict = json.loads(args.c)
        except:
            print("Invalid JSON, using c=1 for all places")
            c_dict = {p: 1 for p in model.place_list}

    # Gọi hàm optimization, truyền thêm bdd_stats và t_start
    optimize_reachable(petri, c_dict, model.place_list, R, model.bdd, bdd_stats, t_start)

if __name__ == "__main__":
    run_cli()