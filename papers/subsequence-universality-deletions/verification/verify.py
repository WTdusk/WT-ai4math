"""SMT proof obligations for subsequence-deletions.tex. Requires z3-solver."""
import itertools
from collections import Counter
import z3 as z

counts = Counter()


def prove(name, assumptions, conclusion):
    solver = z.Solver()
    solver.add(*assumptions, z.Not(conclusion))
    status = solver.check()
    if status != z.unsat:
        raise RuntimeError((name, status, solver.model() if status == z.sat else "unknown"))
    counts[name] += 1


def symbolic_run():
    # Missing letters since the last greedy arch. A run closes an arch
    # exactly if its letter is the unique missing one and a copy survives.
    integer = z.IntSort()
    alphabet, missing = z.Consts("alphabet missing", z.SetSort(integer))
    a, c, other, h, length, level, matched = z.Ints("a c other h length level matched")
    member = z.IsMember
    single = z.SetAdd(z.EmptySet(integer), c)
    closes = z.And(h > 0, missing == single)
    after = z.If(h == 0, missing,
                 z.If(closes, z.If(h == 1, alphabet, z.SetDel(alphabet, c)),
                      z.SetDel(missing, c)))
    new_level = level + z.If(closes, 1, 0)
    base = [z.IsSubset(missing, alphabet), missing != z.EmptySet(integer),
            member(c, alphabet), member(other, alphabet), other != c,
            member(a, alphabet), length >= 1, h >= 0, h <= length, level >= 0]
    # Backward choice of a canonical incoming pointer for every admissible
    # outgoing pointer a. This also shows which of the four table rows applies.
    incoming = z.If(closes, c, a)
    follows = z.Or(z.And(incoming != c, a == incoming, z.Not(closes)),
                   z.And(incoming == c, a == c, h == 0, z.Not(closes)),
                   z.And(incoming == c, a == c, h == 1, closes),
                   z.And(incoming == c, a != c, h >= 1, closes))
    prove("canonical-step", base + [member(a, after)],
          z.And(member(incoming, missing), follows))
    prove("missing-set-nonempty", base, after != z.EmptySet(integer))
    def tick(m):
        return z.If(m == single, alphabet, z.SetDel(m, c))

    # Lift the single-position arch scanner to an arbitrarily long run.
    # after(h+1) must agree with feeding one more c to after(h).
    sub = lambda expr: z.substitute(expr, (h, h+1))
    prove("run-induction-base", base + [h == 0],
          z.And(after == missing, z.Not(closes)))
    prove("run-induction-step", base,
          z.And(sub(after) == tick(after),
                sub(new_level) == new_level + z.If(after == single, 1, 0)))

    # Compare a scan started after x with the scan of y from scratch.
    # Inclusion reverses exactly when one scanner gets an arch ahead.
    cold = z.Const("cold", z.SetSort(integer))
    gap = z.Int("gap")
    def coupled(g, m, n):
        return z.Or(z.And(g == 0, z.IsSubset(m, n)),
                    z.And(g == 1, z.IsSubset(n, m)))

    prove("split-induction-base", base, coupled(0, missing, alphabet))
    prove("split-induction-step", base + [z.IsSubset(cold, alphabet),
          cold != z.EmptySet(integer), coupled(gap, missing, cold)],
          coupled(gap + z.If(missing == single, 1, 0) - z.If(cold == single, 1, 0),
                  tick(missing), tick(cold)))
    prove("single-deletion-coupling", base,
          coupled(z.If(missing == single, 1, 0), tick(missing), missing))
    # Soundness for any normalized pointer path, even a noncanonical one.
    p = z.Int("p")
    invariant = z.And(matched >= level, z.Implies(matched == level, member(p, missing)))
    rows = [(p != c, a == p, h == length, 0),
            (p == c, a == c, h == 0, 0),
            (p == c, a == c, h == 1, 1),
            (p == c, a != c, h == length, 1)]
    for entry, exit_, kept, step in rows:
        new_matched = matched + step
        prove("sound-step", base + [member(p, alphabet), invariant, entry, exit_, kept],
              z.And(new_matched >= new_level,
                    z.Implies(new_matched == new_level, member(a, after))))
    W, M, kept_weight = z.Ints("W M kept_weight")
    prove("retain-maximum", [0 <= kept_weight, kept_weight <= M, M <= W],
          W - M <= W - kept_weight)
    P, S, I, k, b, s = z.Ints("P S I k b s")
    pre = [P >= 0, S >= 0, b >= 0, s >= 0, b <= P, s <= S,
           P + S <= I, b+s <= k, k <= b+s+1]
    low = z.If(k-S-1 > 0, k-S-1, 0)
    high = z.If(k < P, k, P)
    prove("band-containment-and-width", pre, z.And(low <= b, b <= high,
          high-low+1 <= k+1, high-low+1 <= I-k+2))

    # Alternating binary runs: after run i, seed means that its letter
    # has already been seen in the unfinished arch. j=r+1 models no
    # singleton; otherwise the only singleton is at the interior run j.
    r, i, j = z.Ints("r i j")
    family = [r >= 3, z.Or(j == r+1, z.And(j >= 2, j < r))]
    def arches(t):
        return t-1-z.If(j < t, 1, 0)
    prove("binary-family-base", family, z.And(arches(1) == 0, j != 1))
    prove("binary-family-step", family + [i >= 1, i < r],
          z.And(arches(i+1) == arches(i)+z.If(i != j, 1, 0),
                (i+1 != j) == z.Or(i == j, i+1 != j)))
    prove("binary-family-terminal", family, arches(r) == z.If(j == r+1, r-1, r-2))


def index(word, q):
    # Specification independent of arches: enumerate target words and test
    # subsequence membership with an advancing iterator.
    for size in itertools.count(1):
        for target in itertools.product(range(q), repeat=size):
            stream = iter(word)
            if not all(any(x == a for x in stream) for a in target):
                return size - 1


def minimum(values, infinity):
    result = infinity
    for v in values:
        result = z.If(v < result, v, result)
    return result


def check_word(word, q):
    n = len(word)
    I = index(word, q)
    weights = z.Ints(" ".join(f"v{i}" for i in range(n))) if n > 1 else [z.Int("v0")]
    infinity = sum(weights) + 1
    runs = []
    for c, group in itertools.groupby(enumerate(word), key=lambda item: item[1]):
        positions = [i for i, _ in group]
        costs = [weights[i] for i in positions]
        runs.append((c, sum(costs), -minimum([-v for v in costs], 0),
                     index(word[:positions[0]], q), index(word[positions[0]:], q)))
    exact = [[] for _ in range(I+1)]
    for mask in range(1 << n):
        kept = [a for i, a in enumerate(word) if not mask >> i & 1]
        exact[index(kept, q)].append(sum(v for i, v in enumerate(weights) if mask >> i & 1))
    for k in range(I):
        previous = {}
        for b in range(k+1):
            row, last = {}, {}

            def query(c, i):
                p = last.get(c, -1)
                options = [previous.get(j, infinity) for j in range(p+1, i)]
                if p < 0:
                    options.append(0 if b == 0 else infinity)
                else:
                    _, W, M, _, _ = runs[p]
                    options.extend((row.get(p, infinity)+W, previous.get(p, infinity)+W-M))
                return minimum(options, infinity)

            for i, (c, _, _, P, S) in enumerate(runs):
                if max(0, k-S-1) <= b <= min(k, P):
                    row[i] = query(c, i)
                last[c] = i
            if b == k:
                result = minimum([query(c, len(runs)) for c in range(q)], infinity)
                prove("end-to-end", [v >= 0 for v in weights],
                      result == minimum(exact[k], infinity))
            previous = row


if __name__ == "__main__":
    symbolic_run()
    # Canonical representatives under alphabet renaming. Words missing
    # a letter have I=0 and no admissible target.
    for q in (2, 3):
        for n in range(q, 6):
            for word in itertools.product(range(q), repeat=n):
                if tuple(dict.fromkeys(word)) == tuple(range(q)):
                    check_word(word, q)
    print("Z3", z.get_version_string(), "UNSAT by category:", dict(counts))
