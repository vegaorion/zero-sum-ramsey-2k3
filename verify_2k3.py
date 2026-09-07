#!/usr/bin/env python3
"""
Exact Verification of R(2K_3, Z_3) = 8
-------------------------------------
1. Analytically verifies that K_7 contains no zero-sum 2K_3 under the vertex-potential construction.
2. Formulates the zero-sum avoidance on K_8 as a propositional CNF formula (252 vars, 2689 clauses).
3. Executes Z3's CDCL SAT engine to prove UNSAT, establishing R(2K_3, Z_3) <= 8.
4. Exports '2k3_k8.cnf' in standard DIMACS format for independent solver checks.

Dependencies:
    pip install z3-solver
"""

import itertools
import time
from z3 import Solver, Bool, Or, Not, unsat

def verify_k7_analytical():
    print("=" * 65)
    print(" 1. ANALYTICAL LOWER BOUND: R(2K_3, Z_3) >= 8 on K_7")
    print("=" * 65)
    # Potentials: two 1s, five 2s -> total sum S = 12 = 0 mod 3
    potentials = [1, 1, 2, 2, 2, 2, 2]
    S = sum(potentials) % 3
    assert S == 0, "Potential sum must be 0 mod 3"

    triangles = list(itertools.combinations(range(7), 3))
    zero_sum_pairs = 0
    total_pairs = 0

    for i in range(len(triangles)):
        t1 = set(triangles[i])
        for j in range(i + 1, len(triangles)):
            t2 = set(triangles[j])
            if t1.isdisjoint(t2):
                total_pairs += 1
                # Under potentials, triangle edge sum = -(sum of vertex potentials) mod 3
                w1 = (-sum(potentials[v] for v in t1)) % 3
                w2 = (-sum(potentials[v] for v in t2)) % 3
                if (w1 + w2) % 3 == 0:
                    zero_sum_pairs += 1

    print(f"[*] Total disjoint triangle pairs evaluated in K_7: {total_pairs}")
    print(f"[*] Zero-sum copies found: {zero_sum_pairs}")
    assert zero_sum_pairs == 0, "Verification failed!"
    print("[+] PASS: K_7 contains 0 zero-sum copies of 2K_3.")
    print("    Analytical lower bound R(2K_3, Z_3) >= 8 is verified.\n")


def build_and_export_cnf(filename="2k3_k8.cnf"):
    N = 8
    edges = list(itertools.combinations(range(N), 2))
    triangles = list(itertools.combinations(range(N), 3))

    var_id = 1
    edge_var = {}
    for e in edges:
        for c in range(3):
            edge_var[(e, c)] = var_id
            var_id += 1

    tri_var = {}
    for t_idx in range(len(triangles)):
        for r in range(3):
            tri_var[(t_idx, r)] = var_id
            var_id += 1

    total_vars = var_id - 1
    clauses = []

    # 1. Edge exact-one color constraints: 28 edges * 4 clauses = 112
    for e in edges:
        v0, v1, v2 = edge_var[(e, 0)], edge_var[(e, 1)], edge_var[(e, 2)]
        clauses.append([v0, v1, v2])
        clauses.append([-v0, -v1])
        clauses.append([-v0, -v2])
        clauses.append([-v1, -v2])

    # 2. Triangle exact-one residue constraints: 56 triangles * 4 clauses = 224
    for t_idx in range(len(triangles)):
        r0, r1, r2 = tri_var[(t_idx, 0)], tri_var[(t_idx, 1)], tri_var[(t_idx, 2)]
        clauses.append([r0, r1, r2])
        clauses.append([-r0, -r1])
        clauses.append([-r0, -r2])
        clauses.append([-r1, -r2])

    # 3. Triangle definition constraints: 56 triangles * 27 triples = 1512
    for t_idx, tri in enumerate(triangles):
        u, v, w = tri
        e1 = (min(u, v), max(u, v))
        e2 = (min(u, w), max(u, w))
        e3 = (min(v, w), max(v, w))
        for c1 in range(3):
            for c2 in range(3):
                for c3 in range(3):
                    rem = (c1 + c2 + c3) % 3
                    clauses.append([
                        -edge_var[(e1, c1)],
                        -edge_var[(e2, c2)],
                        -edge_var[(e3, c3)],
                        tri_var[(t_idx, rem)]
                    ])

    # 4. Zero-sum avoidance: 280 disjoint pairs * 3 forbidden combinations = 840
    for i in range(len(triangles)):
        t1_set = set(triangles[i])
        for j in range(i + 1, len(triangles)):
            if t1_set.isdisjoint(triangles[j]):
                # Forbid (0, 0), (1, 2), (2, 1)
                clauses.append([-tri_var[(i, 0)], -tri_var[(j, 0)]])
                clauses.append([-tri_var[(i, 1)], -tri_var[(j, 2)]])
                clauses.append([-tri_var[(i, 2)], -tri_var[(j, 1)]])

    # 5. Symmetry breaking: normalize edge (0, 1) to color 0 = 1 clause
    clauses.append([edge_var[((0, 1), 0)]])

    assert total_vars == 252, f"Expected 252 variables, got {total_vars}"
    assert len(clauses) == 2689, f"Expected 2689 clauses, got {len(clauses)}"

    with open(filename, "w") as f:
        f.write("c DIMACS CNF for Zero-Sum Ramsey R(2K_3, Z_3) on K_8\n")
        f.write(f"p cnf {total_vars} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(map(str, cl)) + " 0\n")

    return total_vars, clauses


def solve_k8_z3(total_vars, clauses):
    print("=" * 65)
    print(" 2. COMPUTATIONAL REFUTATION: K_8 VIA Z3 CDCL SAT")
    print("=" * 65)
    print(f"[*] Problem dimensions: {total_vars} variables, {len(clauses)} clauses.")
    print("[*] Launching Z3 solver...")

    s = Solver()
    z3_vars = {i: Bool(f"v_{i}") for i in range(1, total_vars + 1)}

    for cl in clauses:
        literals = [z3_vars[lit] if lit > 0 else Not(z3_vars[-lit]) for lit in cl]
        s.add(Or(literals))

    t0 = time.time()
    result = s.check()
    elapsed = time.time() - t0

    if result == unsat:
        print(f"[+] RESULT: UNSAT (Proved in {elapsed:.3f}s)")
        print("    No edge-weighting of K_8 avoids a zero-sum 2K_3.")
        print("    Upper bound R(2K_3, Z_3) <= 8 is certified.")
        print("\n" + "=" * 65)
        print(" CONCLUSION: R(2K_3, Z_3) = 8 IS PROVED EXACT.")
        print("=" * 65)
    else:
        print(f"[-] Unexpected result: {result}")


if __name__ == "__main__":
    verify_k7_analytical()
    n_vars, clauses = build_and_export_cnf("2k3_k8.cnf")
    solve_k8_z3(n_vars, clauses)