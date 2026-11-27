"""Check the positive miter, each output branch of the negative miter, and a witness."""

import argparse
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path

import projection_sat as sat


def run(args):
    queries = sat.ProjectionQueries(args.base, args.t)
    field, circuit, masks, terms = queries.field, queries.circuit, queries.masks, queries.terms
    hashes = hashlib.sha256()
    cases = [("positive", None)] + [("negative", j) for j in range(len(terms))]
    with tempfile.TemporaryDirectory() as scratch:
        path = Path(scratch)
        proof = path/"query.lrat"
        cnf = path/"query.cnf"
        for mode, branch in cases:
            queries.query(mode, args.t, branch).write(cnf)
            solve = subprocess.run([args.solver, "-q", "--lrat", str(cnf), str(proof)],
                                   capture_output=True, timeout=args.timeout)
            if solve.returncode != 20:
                raise RuntimeError((mode, branch, solve.returncode, solve.stdout[:250]))
            check = subprocess.run([args.checker, "-q", str(cnf), str(proof)],
                                   capture_output=True, timeout=args.timeout)
            if check.returncode not in (0,20) or b"s VERIFIED" not in check.stdout.splitlines():
                raise RuntimeError((mode, branch, check.returncode, check.stderr[:250]))
            for name in (cnf, proof):
                hashes.update(hashlib.sha256(name.read_bytes()).digest())
            if branch is not None and (branch+1) % 100 == 0:
                print(f"Independently replayed {branch+1} of {len(terms)} negative branches", flush=True)
        sharp = queries.query("negative", args.t+1)
        sharp.write(cnf)
        solve = subprocess.run([args.solver, "-q", str(cnf)], capture_output=True,
                               text=True, timeout=args.timeout)
        if solve.returncode != 10:
            raise RuntimeError(("sharpness query", solve.returncode))
        literal_values = [int(w) for line in solve.stdout.splitlines() if line.startswith("v ")
                          for w in line.split()[1:] if int(w)]
        true_variables = {v for v in literal_values if v > 0}
        assert len({abs(w) for w in literal_values}) == sharp.variables
        assert all(any((abs(w) in true_variables) == (w > 0) for w in clause) for clause in sharp.clauses)
        raw = [int(j+1 in true_variables) for j in range(circuit.inputs)]
        n = len(masks)
        active = [w for w in range(n) if raw[n+w]]
        points = sum(1 << p for p in range(n) if raw[p])
        assert len(active) == args.t+1 and all(points & masks[w] == 0 for w in active)
        assert circuit.evaluate(raw) == 1
        result = dict(q=field.q, budget=args.t, inputs=circuit.inputs, gates=len(circuit.gates),
                      checked_unsat=len(cases), negative_branches=len(terms),
                      cnf_and_proof_digest=hashes.hexdigest(), witness_lines=active,
                      witness_point_count=sum(raw[:n]))
        print(json.dumps(result, sort_keys=True), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("base", type=int)
    parser.add_argument("t", type=int)
    parser.add_argument("--solver", default="cadical")
    parser.add_argument("--checker", default="lrat-trim")
    parser.add_argument("--timeout", type=int, default=120, help="seconds per solver or checker process")
    if not __debug__:
        raise SystemExit("Run Python without -O so the final SAT witness is verified.")
    run(parser.parse_args())
