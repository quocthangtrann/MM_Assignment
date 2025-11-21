MM_Assignment — Petri Net Reachability, BDD, ILP Optimization

This project implements all five tasks of the CO2011 / MM-251 Mathematical Modeling assignment at HCMUT:

PNML parsing

Explicit reachability (BFS)

Symbolic reachability using BDD

Deadlock detection (BDD + ILP)

Optimization over reachable markings

The system provides a complete analysis pipeline for 1-safe Petri nets, integrating classical explicit search and symbolic techniques (BDD + ILP).

📦 Installation

1️⃣ Install dependencies

The project uses Python 3.9+.

pip3 install -r requirements.txt

Replace philo.pnml with any Petri net in PNML format.

▶️ How to run?

✔ Run all 5 tasks at once:

python3 main.py philo.pnml

✔ Compare Explicit BFS vs BDD Symbolic Reachability:

python3 bdd_reachability.py philo.pnml --compare

✔ Dump all reachable markings (729 in philo example):

python3 bdd_reachability.py philo.pnml --dump

