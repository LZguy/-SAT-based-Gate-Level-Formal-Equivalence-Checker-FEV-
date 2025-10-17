# SAT-based Gate-Level Formal Equivalence Checker (FEV)

Formal Equivalence Verification between two **gate-level Verilog** designs using a
SAT solver (**MiniSat**) and the **HCM – Hierarchical Connectivity Model** library  
for parsing/flattening the netlists and extracting PIs/POs.

> ⚠️ Note: Course handouts are **not included** here (copyright).  
> This repo contains **my code and report only**.  
> HCM is a Technion library — external users may not have access. See:
> https://focused-lalande-5a6539.netlify.app/index.html

---

## Overview

- Parse structural Verilog for **spec** and **impl**, flatten with HCM, collect **PIs/POs**. :contentReference[oaicite:0]{index=0}  
- Encode each flattened netlist to CNF (Tseytin-style per gate), handle **VDD/VSS** constants.  
- Build a **miter**: for every PO pair add a “diff” variable (XOR), and require at least one diff = 1.  
- Run MiniSat: **UNSAT ⇒ equivalent**, **SAT ⇒ counter-example** input assignment printed. 

---

## Project Structure

```
fev-wet03/
├─ docs/
│ └─ HW3.pdf # my report
├─ src/
│ ├─ HW3ex1.cc # my implementation (uses HCM + MiniSat API)
│ └─ minisat_api_example.cpp # MiniSat API demo (MIT-licensed example)
├─ examples/
│ ├─ example.cnf.txt # tiny DIMACS demo
│ └─ place course benchmark files if you have access (optional)
├─ tools/
│ └─ Makefile # build (uses system HCM/MiniSat includes/libs)
├─ .gitignore
├─ LICENSE
└─ README.md
```

---

## Build

This project assumes HCM and MiniSat headers/libs are installed and visible to the compiler.
The included `Makefile` expects the same layout used in the course VM.

```bash
cd src
make
```
If you can’t link against HCM on your machine, build will fail (by design) — this code is
kept here mainly for portfolio/reference.

---
## Usage

Run the FEV tool on two gate-level designs (spec vs impl). The program:
1. parses and flattens both designs with HCM,
2. generates CNF for each, builds a miter,
3. calls MiniSat; if SAT, prints a counter-example for PIs, else prints equivalence,
4. also writes the combined CNF to <top>.cnf.

Example commands used for self-tests (c1355/c1356 → UNSAT; c0409/c0410 → SAT):

```bash
./gl_verilog_fev -s TopLevel1355 stdcell.v c1355.v  -i TopLevel1356 stdcell.v c1356.v
./gl_verilog_fev -s TopLevel0409 stdcell.v c0409.v  -i TopLevel0410 stdcell.v c0410.v
```
These are the official lines from the assignment’s self-test section.

---
## Key Implementation Notes

- Port extraction & matching: compare sorted PI/PO name lists; if they differ, report non-equivalence immediately.
- Constants: creating a SAT var for VDD/VSS and adding unit clauses to force 1/0.
- Gate encodings (sketch):
  - buffer: Z ↔ A (two clauses)
  - inv: Z ↔ ~A (two clauses)
  - and/or/nand/nor: standard Tseytin forms with support for N-ary inputs
  - xor (2-input): 4-clause encoding of Z ↔ A ⊕ B (shown verbatim in the report)
- Miter: for each PO pair add a fresh d_i with d_i ↔ (spec_i ⊕ impl_i); add a clause ∨_i d_i.

---

## MiniSat API Example

A minimal example building the same CNF as the included example.cnf.txt is provided
(minisat_api_example.cpp) under the MiniSat MIT license (copyright headers inside).
It demonstrates adding variables/clauses and solving.

---
## Artifacts / Data

- docs/HW3.pdf — my write-up with algorithm details and XOR Tseytin proof.
- examples/example.cnf.txt — small DIMACS file you can solve to verify your MiniSat build. 

Course files (assignment PDF, stdcell.v, benchmark netlists) are not included.
