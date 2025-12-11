# MM_Assignment — Petri Net Reachability, BDD, ILP Optimization

## Project Overview
This project implements all five tasks of the **CO2011 / MM-251 Mathematical Modeling** assignment at HCMUT.  
It provides a complete analysis pipeline for **1-safe Petri Nets**, combining both explicit and symbolic methods to compute reachability, detect deadlocks, and solve optimization problems.

The system supports:
- **PNML Parsing**  
- **Explicit Reachability (BFS)**  
- **Symbolic Reachability using BDD**  
- **Deadlock Detection (BDD + ILP)**  
- **Optimization over reachable markings**  

This framework demonstrates how modern symbolic techniques (Binary Decision Diagrams and Integer Linear Programming) significantly improve scalability over classical explicit-state search.

---

## System Architecture
The system is modularized into four main components:

- **PNML Processor**  
  Parses a PNML Petri Net file and constructs internal graph structures (places, transitions, incidence matrix).

- **Explicit Reachability Engine**  
  Implements state-space exploration using classical BFS, enumerating all reachable markings.

- **Symbolic BDD Reachability**  
  Represents transition relations and reachable markings as Boolean functions, enabling compact symbolic traversal.

- **ILP-based Deadlock & Optimization Engine**  
  Formulates deadlock constraints and optimization objectives as ILP problems using the reachable markings.

---

## Installation

### 1️⃣ Install Dependencies  
The project requires **Python 3.9+**.

```bash
pip3 install -r requirements.txt
```

2️⃣ Input Petri Net

Replace philo.pnml with any Petri Net in standard PNML format.

---
## Build and Execution
✔ Run all 5 tasks sequentially:
```bash
python3 main.py philo.pnml
```
✔ Compare Explicit BFS vs Symbolic BDD Reachability:
```bash
python3 bdd_reachability.py philo.pnml --compare
```
✔ Dump all reachable markings (e.g., 729 for the philosopher model):
```bash
python3 bdd_reachability.py philo.pnml --dump
```
