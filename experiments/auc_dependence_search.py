"""
Brute-force check of Proposition auc_improper (c)-(d): how often, and by how much, the truthful
ranking fails to maximise the expected AUC when the labels of the units are dependent.

For n = 3 and n = 4 units, draw joint laws over the 2^n label vectors from a flat Dirichlet
distribution, compute the expected AUC (half credit for ties, AUC = 0 when n+ n- = 0) of the
truthful ranking (by the marginals) and of every strict ordering, and record the gap to the best
ordering. Part (c) predicts no failure for n = 3; part (d) shows that failures exist for n >= 4.
Seed 0, 3000 laws per n. Prints the failure counts and the gap distribution.
"""
import itertools

import numpy as np

SEED, DRAWS = 0, 3000


def expected_auc(score, labels, probs):
    total = 0.0
    for y, pw in zip(labels, probs):
        npos = sum(y)
        nneg = len(y) - npos
        if npos == 0 or nneg == 0:
            continue
        c = sum(1.0 if score[i] > score[j] else 0.5 if score[i] == score[j] else 0.0
                for i in range(len(y)) if y[i] for j in range(len(y)) if not y[j])
        total += pw * c / (npos * nneg)
    return total


def main():
    rng = np.random.default_rng(SEED)
    for n in (3, 4):
        labels = list(itertools.product([0, 1], repeat=n))
        perms = list(itertools.permutations(range(n)))
        fails, gaps = 0, []
        for _ in range(DRAWS):
            probs = rng.dirichlet(np.ones(len(labels)))
            p = np.array([sum(pw * y[i] for y, pw in zip(labels, probs)) for i in range(n)])
            truth = expected_auc(p, labels, probs)
            best = max(expected_auc([n - perm.index(i) for i in range(n)], labels, probs) for perm in perms)
            if best > truth + 1e-12:
                fails += 1
                gaps.append(best - truth)
        g = np.array(gaps) if gaps else np.zeros(1)
        print(f"n={n}: truthful not optimal in {fails} of {DRAWS} laws; "
              f"gap median {np.median(g):.4f}, 95th percentile {np.quantile(g, 0.95):.4f}, max {g.max():.4f}")


if __name__ == "__main__":
    main()
