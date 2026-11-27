"""Exhaustive checks for the window-length criterion and cyclic outage formula."""

from itertools import combinations
from math import gcd


def window_counts(points, size, length):
    occupied = set(points)
    return [sum((x + i) % size in occupied for i in range(length))
            for x in range(size)]


def predicted(size, weight, lengths):
    common = gcd(size, weight)
    period, numerator = size // common, weight // common
    periods = [length for length in lengths if length % period == 0]
    shape = min(numerator, period - numerator) == 1 or any(
        numerator * length % period in (1, period - 1) for length in lengths)
    return gcd(size, *periods) == period and shape


def check_criteria():
    layouts = families = 0
    for size in range(2, 13):
        full = (1 << (size - 1)) - 1
        for weight in range(1, size):
            bad = bytearray(full + 1)
            for points in combinations(range(size), weight):
                passed = 0
                for length in range(1, size):
                    counts = window_counts(points, size, length)
                    if max(counts) - min(counts) <= 1:
                        passed |= 1 << (length - 1)
                if passed != full:
                    bad[passed] = 1
                layouts += 1
            # Every subset of a mask passed by a counterexample is also bad.
            for bit in range(size - 1):
                for mask in range(full + 1):
                    if mask & (1 << bit) and bad[mask]:
                        bad[mask ^ (1 << bit)] = 1
            for mask in range(full + 1):
                lengths = [i for i in range(1, size) if mask & (1 << (i - 1))]
                assert predicted(size, weight, lengths) == (not bad[mask])
                families += 1
    return layouts, families


def check_outages():
    cases = 0
    for size in range(2, 9):
        for weight in range(1, size):
            # Average each fixed live/dead pattern over its weight cyclic shifts.
            for live in range(1 << weight):
                void = [sum(all(not (live >> ((j+i) % weight) & 1)
                                for i in range(k)) for j in range(weight))
                        for k in range(weight + 1)]
                for points in combinations(range(size), weight):
                    misses = [0] * size
                    for shift in range(weight):
                        active = {pos for j, pos in enumerate(points)
                                  if live >> ((j+shift) % weight) & 1}
                        for x in range(size):
                            for length in range(1, size + 1):
                                if (x + length - 1) % size in active:
                                    break
                                misses[length-1] += 1
                    for length, actual in enumerate(misses, start=1):
                        counts = window_counts(points, size, length)
                        q, rem = divmod(weight * length, size)
                        best = (size-rem) * void[q]
                        if rem:
                            best += rem * void[q+1]
                        assert actual == sum(void[k] for k in counts)
                        assert actual >= best
                        if max(counts) - min(counts) <= 1:
                            assert actual == best
                        cases += 1
    return cases


if __name__ == "__main__":
    print("layouts, length families:", check_criteria())
    print("placement/outage-pattern/window cases:", check_outages())
