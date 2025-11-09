from __future__ import annotations
import argparse
import json
import time
import tracemalloc
from collections import deque
from typing import Dict, List, Tuple, Set

# Import parser from Task 1
try:
    from pnml_parser import parse_pnml_file, SAMPLE_PNML
    import xml.etree.ElementTree as ET
except Exception as e:
    raise ImportError("Failed importing pnml_parser. Make sure pnml_parser.py is in the same folder.") from e


# ---------- Data structures & helpers ----------

def build_index_maps(places: Dict[str, object]) -> Tuple[List[str], Dict[str, int]]:
    """
    Build ordered list of place ids and mapping place_id -> bit index (0..n-1).
    Returns (place_list, place_to_index).
    """
    place_list = sorted(places.keys())  # deterministic order
    place_to_index = {pid: i for i, pid in enumerate(place_list)}
    return place_list, place_to_index


def marking_dict_to_bitmask(marking: Dict[str, int], place_to_index: Dict[str, int]) -> int:
    """Convert dict place->token (int) to bitmask int (LSB = index 0)."""
    mask = 0
    for pid, tokens in marking.items():
        if tokens not in (0, 1):
            raise ValueError(f"Non 1-safe marking value {tokens} at place {pid}. Task assumes 1-safe nets.")
        if tokens == 1:
            idx = place_to_index[pid]
            mask |= (1 << idx)
    return mask


def bitmask_to_marking_dict(mask: int, place_list: List[str]) -> Dict[str, int]:
    """Convert bitmask back to dict place->0/1 according to place_list order."""
    d = {}
    for idx, pid in enumerate(place_list):
        d[pid] = 1 if ((mask >> idx) & 1) else 0
    return d


def build_transition_masks(petri_net) -> Tuple[List[int], List[int], List[str]]:
    """
    Build for each transition:
      - pre_mask: bitmask of places that are consumed (inputs)
      - post_mask: bitmask of places that are produced (outputs)
      - transition_order: list of transition ids in deterministic order
    Note: this assumes arc weights are 1 (or no inscription); if an arc has weight >1 we raise error
    because we store marking as 0/1 bits for 1-safe nets.
    """
    # collect arcs into adjacency
    pre_sets: Dict[str, Set[str]] = {}
    post_sets: Dict[str, Set[str]] = {}
    # ensure keys exist for every transition
    for tid in petri_net.transitions.keys():
        pre_sets[tid] = set()
        post_sets[tid] = set()

    for arc in petri_net.arcs:
        src = arc.source
        tgt = arc.target
        # If arc goes place -> transition, it's an input (pre)
        if src in petri_net.places and tgt in petri_net.transitions:
            # weight check
            if getattr(arc, 'inscription', 1) != 1:
                raise ValueError("Arc weight != 1 found. This explicit BFS assumes 1-safe nets with weight 1.")
            pre_sets[tgt].add(src)
        # If arc goes transition -> place, it's an output (post)
        elif src in petri_net.transitions and tgt in petri_net.places:
            if getattr(arc, 'inscription', 1) != 1:
                raise ValueError("Arc weight != 1 found. This explicit BFS assumes 1-safe nets with weight 1.")
            post_sets[src].add(tgt)
        else:
            # arcs between place->place or transition->transition are invalid for PT nets
            raise ValueError(f"Arc {arc.id} has unexpected endpoints: {src} -> {tgt}")

    # deterministic order for transitions
    transition_order = sorted(petri_net.transitions.keys())
    pre_masks = []
    post_masks = []
    # place ordering
    place_list, place_to_index = build_index_maps(petri_net.places)
    for tid in transition_order:
        pre_mask = 0
        post_mask = 0
        for p in pre_sets.get(tid, ()):
            pre_mask |= (1 << place_to_index[p])
        for p in post_sets.get(tid, ()):
            post_mask |= (1 << place_to_index[p])
        pre_masks.append(pre_mask)
        post_masks.append(post_mask)
    return pre_masks, post_masks, transition_order


def is_enabled(marking_mask: int, pre_mask: int) -> bool:
    """A transition is enabled if all places in pre_mask have tokens (bitwise)."""
    return (marking_mask & pre_mask) == pre_mask


def fire_transition(marking_mask: int, pre_mask: int, post_mask: int) -> int:
    """
    Fire transition: remove tokens in pre_mask and add tokens in post_mask
    For 1-safe nets we can simply clear pre bits and set post bits.
    """
    # remove pre tokens
    after = marking_mask & (~pre_mask)
    # add post tokens
    after |= post_mask
    return after


# ---------- BFS exploration ----------

def explicit_bfs(petri_net, limit: int = 0) -> Tuple[Set[int], List[Tuple[int, int]]]:
    """
    Perform BFS from initial marking.
    Returns (reachable_set_of_masks, transitions_fired_list)
    transitions_fired_list collects tuples (from_mask, to_mask) for each discovered edge (useful for building explicit graph).
    If limit > 0: stop after finding `limit` distinct states (useful to avoid explosion).
    """
    place_list, place_to_index = build_index_maps(petri_net.places)
    initial_mask = marking_dict_to_bitmask(petri_net.initial_marking, place_to_index)

    pre_masks, post_masks, transition_order = build_transition_masks(petri_net)

    visited: Set[int] = set()
    visited.add(initial_mask)
    q = deque([initial_mask])
    transitions_edges: List[Tuple[int, int]] = []

    while q:
        cur = q.popleft()
        # for each transition in order
        for pre_mask, post_mask in zip(pre_masks, post_masks):
            if is_enabled(cur, pre_mask):
                nxt = fire_transition(cur, pre_mask, post_mask)
                transitions_edges.append((cur, nxt))
                if nxt not in visited:
                    visited.add(nxt)
                    q.append(nxt)
                    if limit and len(visited) >= limit:
                        return visited, transitions_edges
    return visited, transitions_edges


# ---------- CLI & main ----------

def pretty_print_markings(masks: Set[int], place_list: List[str], sample: int = 10):
    """Print a few example markings and counts."""
    print(f"Total reachable markings: {len(masks)}")
    sorted_masks = sorted(masks)
    print(f"Example first {min(sample, len(sorted_masks))} markings (as dict place->0/1):")
    for m in sorted_masks[:sample]:
        print("  ", bitmask_to_marking_dict(m, place_list))


def run_on_pnml_path(path: str, out_path: str = None, limit: int = 0):
    # parse file
    petri = parse_pnml_file(path)
    place_list, place_to_index = build_index_maps(petri.places)

    # sanity check 1-safe initial markings
    for pid, val in petri.initial_marking.items():
        if val not in (0, 1):
            raise ValueError(f"Initial marking not 1-safe: place {pid} has {val} tokens")

    # measure time & peak memory
    tracemalloc.start()
    t0 = time.perf_counter()
    reachable, edges = explicit_bfs(petri, limit=limit)
    t1 = time.perf_counter()
    current, peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()

    print(f"Exploration finished in {t1 - t0:.4f} seconds.")
    print(f"Peak memory during exploration: {peak / 1024:.1f} KiB")
    place_list, _ = build_index_maps(petri.places)
    pretty_print_markings(reachable, place_list)

    if out_path:
        # export reachable as list of dict markings
        out_list = []
        for mask in sorted(reachable):
            out_list.append({'mask': mask, 'marking': bitmask_to_marking_dict(mask, place_list)})
        with open(out_path, 'w', encoding='utf-8') as f:
            json.dump({
                'net_id': petri.id,
                'n_places': len(place_list),
                'n_transitions': len(petri.transitions),
                'n_reachable': len(reachable),
                'reachable': out_list
            }, f, indent=2, ensure_ascii=False)
        print(f"Wrote reachable markings to {out_path}")


def run_cli():
    parser = argparse.ArgumentParser(description="Explicit reachability (BFS) for 1-safe Petri nets.")
    parser.add_argument('file', nargs='?', help='PNML input file path (omitting uses --test).')
    parser.add_argument('--out', '-o', help='Write reachable markings to JSON.')
    parser.add_argument('--test', action='store_true', help='Run using built-in SAMPLE_PNML from pnml_parser.')
    parser.add_argument('--limit', type=int, default=0, help='Limit number of reachable states (0 = no limit).')
    args = parser.parse_args()

    if args.test:
        # parse SAMPLE_PNML string from pnml_parser
        root = ET.fromstring(SAMPLE_PNML)
        petri = parse_pnml_file  # alias to ensure import
        # Use parser but from string; simpler to call PNMLParser directly:
        from pnml_parser import PNMLParser
        pn = PNMLParser(root).parse()
        # Save a quick temp JSON? Just run BFS
        run_on_pnml_path_for_parsedpn(pn, args.out, args.limit)
        return

    if not args.file:
        parser.print_help()
        return
    run_on_pnml_path(args.file, args.out, args.limit)


def run_on_pnml_path_for_parsedpn(parsed_pn, out_path: str = None, limit: int = 0):
    """
    Helper to run BFS when you already have parsed PetriNet object (used by --test).
    This duplicates some logic from run_on_pnml_path but accepts parsed object.
    """
    petri = parsed_pn
    place_list, place_to_index = build_index_maps(petri.places)

    # sanity check 1-safe initial markings
    for pid, val in petri.initial_marking.items():
        if val not in (0, 1):
            raise ValueError(f"Initial marking not 1-safe: place {pid} has {val} tokens")

    tracemalloc.start()
    t0 = time.perf_counter()
    reachable, edges = explicit_bfs(petri, limit=limit)
    t1 = time.perf_counter()
    current, peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()

    print(f"Exploration finished in {t1 - t0:.4f} seconds.")
    print(f"Peak memory during exploration: {peak / 1024:.1f} KiB")
    pretty_print_markings(reachable, place_list)

    if out_path:
        out_list = []
        for mask in sorted(reachable):
            out_list.append({'mask': mask, 'marking': bitmask_to_marking_dict(mask, place_list)})
        with open(out_path, 'w', encoding='utf-8') as f:
            json.dump({
                'net_id': petri.id,
                'n_places': len(place_list),
                'n_transitions': len(petri.transitions),
                'n_reachable': len(reachable),
                'reachable': out_list
            }, f, indent=2, ensure_ascii=False)
        print(f"Wrote reachable markings to {out_path}")


if __name__ == '__main__':
    run_cli()