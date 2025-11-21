#!/usr/bin/env python3
import sys
import subprocess
import time
import os

TASKS = [
    ("Task 1: PNML Parsing", "pnml_parser.py"),
    ("Task 2: Explicit Reachability", "explicit_reachability.py"),
    ("Task 3: BDD Reachability", "bdd_reachability.py"),
    ("Task 4: Deadlock Detection (BDD + ILP)", "deadlock_detection.py"),
    ("Task 5: Optimization over Reachable Markings", "optimization.py"),
]

def run_task(title, script, input_file):
    print("\n" + "="*80)
    print(f"▶ {title}")
    print("="*80)

    if not os.path.exists(script):
        print(f"ERROR: file {script} not found!")
        return

    start = time.time()
    try:
        result = subprocess.run(
            ["python3", script, input_file],
            text=True,
            capture_output=True
        )
        end = time.time()

        # Print STDOUT
        print(result.stdout)

        # Print STDERR only if exists
        if result.stderr.strip():
            print("\n[stderr]:")
            print(result.stderr)

        #print(f"⏱ Execution time: {end - start:.4f} seconds")

    except Exception as e:
        print(f"Exception while running {script}: {e}")

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 main.py <input.pnml>")
        sys.exit(1)

    input_file = sys.argv[1]

    if not os.path.exists(input_file):
        print(f"Input file not found: {input_file}")
        sys.exit(1)

    print("\n==============================")
    print("   CO2011 - MM251 Assignment  ")
    print("   Full Pipeline (Tasks 1 → 5)")
    print("==============================\n")

    for title, script in TASKS:
        run_task(title, script, input_file)

    print("\nCompleted all 5 tasks!")
    print("=============================================================")

if __name__ == "__main__":
    main()
