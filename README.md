# Exact Zero-Sum Ramsey Numbers of Disjoint Triangles Modulo 3

> **Main Result:** For all $s \ge 2$:
> 
> ```
> R(sK₃, ℤ₃) = 3s + 2
> ```

This repository provides the formal verification code, CNF formula, and research paper establishing the exact zero-sum Ramsey numbers for collections of $s \ge 2$ vertex-disjoint triangles over $\mathbb{Z}_3$.

This settles the multi-component triangle family of **Problem 4** from Caro & Mifsud ([arXiv:2502.03864](https://arxiv.org/abs/2502.03864)). It demonstrates that the additive surplus:

$$\Delta(G) = R(G, \mathbb{Z}_3) - |V(G)|$$

collapses from **+8** for a single triangle ($K_3$) down to **+2** for all $s \ge 2$, matching the universal upper bound for acyclic forests.

---

## The Three Pillars of the Proof

1. **Universal Lower Bound (`R(sK₃, ℤ₃) ≥ 3s + 2` for all `s ≥ 1`):**  
   Proven analytically using vertex potentials on `K_(3s+1)`. By assigning potential `2` to exactly two vertices and potential `1` to the remaining `3s - 1` vertices, the total sum is `3s + 3 ≡ 0 (mod 3)`. Every copy of `sK₃` omits one non-zero vertex, forcing its edge weight to be non-zero modulo 3.

2. **Certified Base Case (`R(2K₃, ℤ₃) = 8`):**  
   The existence of an avoidance coloring on `K₈` is encoded as an exact boolean CNF formula (252 variables, 2,689 clauses). Modern CDCL SAT solvers (Z3, CaDiCaL) refute the formula as **UNSATISFIABLE** in under 0.2 seconds, proving `R(2K₃, ℤ₃) ≤ 8`.

3. **Inductive Reduction (`R(sK₃, ℤ₃) ≤ 3s + 2` for all `s ≥ 2`):**  
   For any host complete graph on `N = 3(s+1) + 2 ≥ 11` vertices, the single-triangle threshold `R(K₃, ℤ₃) = 11` guarantees a zero-sum triangle. Removing it leaves `3s + 2` vertices, which contains a zero-sum `sK₃` by induction.

---

## Repository Files

| File | Description |
| :--- | :--- |
| `sk3.pdf` | Complete research paper with proofs, potential calculations, and acknowledgments. |
| `verify_sk3.py` | Automated Python verification suite using Z3 (tests lower bound, SAT base case, and induction invariants). |
| `2k3_k8.cnf` | Exact 2,689-clause propositional formula in standard DIMACS format proving `R(2K₃, ℤ₃) ≤ 8`. |

---

## Quickstart & Verification

### 1. Requirements
Ensure Python 3.8+ is installed, then install the Z3 solver:
```bash
pip install z3-solver
```

### 2. Run Verification
Execute the verification suite:
```bash
python verify_sk3.py
```

Expected output:
```text
=================================================================
 1. SECTION 2: VERIFYING GENERAL POTENTIAL LOWER BOUND
[*] Tested s=1 on K_4: 4 disjoint copies evaluated. Zero-sum: 0.
[*] Tested s=2 on K_7: 140 disjoint copies evaluated. Zero-sum: 0.
[*] Verified s=3 on K_10: Omits vertex w with a_w in {1, 2} != 0 mod 3.
[+] PASS: Proposition 2.1 verified. R(sK_3, Z_3) >= 3s + 2.

 2. SECTION 3: BASE CASE REFUTATION ON K_8 VIA Z3 SAT
[+] PASS: K_8 is UNSAT in 0.18s. Proposition 3.1 verified.

 3. SECTION 4: VERIFYING INDUCTIVE REDUCTION INVARIANTS
[*] s=2 -> s+1=3: Host K_11 >= 11 (peels K_3), leaving K_8 (by induction).
[+] PASS: Inductive step invariants hold for all s >= 2.
=================================================================
 CONCLUSION: R(sK_3, Z_3) = 3s + 2 IS VERIFIED FOR ALL s >= 2.
=================================================================
```

### 3. Independent SAT Solver Check
You can independently check the raw DIMACS file using any standalone CDCL SAT solver (e.g., [CaDiCaL](https://github.com/arminbiere/cadical)):
```bash
cadical 2k3_k8.cnf
```
The solver returns `s UNSATISFIABLE` in tenths of a second.

---

## Acknowledgments

The author is deeply grateful to Professor Yair Caro for valuable guidance and for suggesting the inductive reduction step peeling off zero-sum triangles.
