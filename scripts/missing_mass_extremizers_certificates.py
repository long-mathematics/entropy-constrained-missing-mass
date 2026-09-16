#!/usr/bin/env python3
"""Exact rational certificates for Appendix D of the accompanying manuscript.

Manuscript: missing_mass_extremizers.tex
Run:       python3 missing_mass_extremizers_certificates.py
Requires:  Python 3.10+; standard library only.

Every entropy root is bracketed between adjacent rationals with denominator
10**30. Logarithms are bounded by a positive series with an explicit tail.
Objective values and all comparisons use Fraction arithmetic; no floating-
point arithmetic is used in verification. Runtime checks remain enabled
under python -O. The finite-cutoff theorem in the manuscript supplies the
analytic justification for exhaustiveness of the candidate lists.
"""
from fractions import Fraction as Q
from functools import lru_cache

Interval = tuple[Q, Q]
Label = tuple[str, int]
DEN = 10**30


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


@lru_cache(maxsize=None)
def log_bounds(x: Q, terms: int = 40) -> Interval:
    """Rational lower and upper bounds for log(x), x > 0."""
    x = Q(x)
    if x <= 0 or terms < 1:
        raise ValueError("Require x > 0 and a positive number of terms")
    exponent = 0
    while x < 1:
        x *= 2
        exponent -= 1
    while x >= 2:
        x /= 2
        exponent += 1

    def series(v: Q) -> Interval:
        # log((1+v)/(1-v)) = 2 sum_{j>=0} v**(2*j+1)/(2*j+1).
        v2, term, total = v*v, v, Q(0)
        for j in range(terms):
            total += term / (2*j+1)
            term *= v2
        total *= 2
        remainder = 2*term / ((2*terms+1)*(1-v2))
        return total, total+remainder

    lo, hi = series((x-1)/(x+1))
    if exponent:
        lo2, hi2 = series(Q(1, 3))
        if exponent > 0:
            lo, hi = lo+exponent*lo2, hi+exponent*hi2
        else:
            # Multiplication by a negative exponent reverses the bounds.
            lo, hi = lo+exponent*hi2, hi+exponent*lo2
    return lo, hi


def entropy_bounds(z: Q, m: int) -> Interval:
    """Bounds for E_m(z), with 0 < z < 1 and m >= 1."""
    if not (0 < z < 1) or m < 1:
        raise ValueError("Require 0 < z < 1 and m >= 1")
    lz, uz = log_bounds(z)
    lw, uw = log_bounds(1-z)
    lm, um = log_bounds(Q(m))
    return (-z*uz-(1-z)*uw+(1-z)*lm,
            -z*lz-(1-z)*lw+(1-z)*um)


def objective_bounds(a: Q, b: Q, m: int, t: int) -> Interval:
    """Bounds for V_{m,t}(z) on a <= z <= b, for integer t >= 1."""
    if not (0 <= a <= b <= 1) or m < 1 or t < 1:
        raise ValueError("Invalid objective-bound parameters")
    # Bound each nonnegative weight and base separately.
    return (a*(1-b)**t+(1-b)*(1-(1-a)/m)**t,
            b*(1-a)**t+(1-a)*(1-(1-b)/m)**t)


def ceil_fraction(x: Q) -> int:
    return -((-x.numerator)//x.denominator)


def decimal_interval(bounds: Interval, digits: int = 12) -> str:
    """Outward-rounded decimal display, without floating-point conversion."""
    scale = 10**digits
    lo, hi = bounds
    a = (lo.numerator*scale)//lo.denominator
    b = -((-hi.numerator*scale)//hi.denominator)

    def fmt(n: int) -> str:
        sign = "-" if n < 0 else ""
        n = abs(n)
        return sign+str(n//scale)+"."+str(n % scale).zfill(digits)

    return "["+fmt(a)+", "+fmt(b)+"]"


# (entropy, sample size, k, M, (branch, m, root numerator) entries, winner)
CASES = [('11/10',
  3,
  3,
  5,
  [('light', 3, 160660804849263531983686271),
   ('heavy', 3, 608188778639135398776642818398),
   ('heavy', 4, 665998836163123097849000253302),
   ('heavy', 5, 697427458105719731466509624915)],
  ('light', 3)),
 ('6/5',
  3,
  3,
  5,
  [('light', 3, 29833600906100072225946038552),
   ('heavy', 3, 536248550668522304908437585659),
   ('heavy', 4, 615098243302302211840804002882),
   ('heavy', 5, 654801099196794560393206420059)],
  ('heavy', 3)),
 ('7/5',
  3,
  4,
  6,
  [('light', 4, 2434107615234567484736411213),
   ('heavy', 4, 489968275298054639002161041831),
   ('heavy', 5, 556791093322619521672138548100),
   ('heavy', 6, 595298369198405264916788686747)],
  ('light', 4)),
 ('19/8',
  8,
  10,
  20,
  [('light', 10, 36297110060081469492248571198),
   ('heavy', 10, 158182736874701865234336967770),
   ('heavy', 11, 238776297033637053215448658873),
   ('heavy', 12, 284566573285913922095326805220),
   ('heavy', 13, 317804706332400439560187652515),
   ('heavy', 14, 343937132264853115880129584166),
   ('heavy', 15, 365395674565682433425720876949),
   ('heavy', 16, 383522857982534038517095410702),
   ('heavy', 17, 399150723485684704025587702561),
   ('heavy', 18, 412834574755180149157030991984),
   ('heavy', 19, 424964808774262438141438087892),
   ('heavy', 20, 435826756675367683720690492011)],
  ('heavy', 14))]


def main() -> None:
    results: dict[tuple[str, int], dict[Label, Interval]] = {}
    for hs, t, k, cutoff, roots, expected_winner in CASES:
        h = Q(hs)
        require(log_bounds(Q(k))[1] < h < log_bounds(Q(k+1))[0],
                "Entropy-index check failed: "+hs)
        require(cutoff == max(k, ceil_fraction(t*h+1)),
                "Cutoff check failed: "+hs)
        labels = {("light", k)} | {("heavy", m) for m in range(k, cutoff+1)}
        require({(branch, m) for branch, m, _ in roots} == labels,
                "Incomplete candidate list: "+hs)
        require(len(roots) == len(labels), "Duplicate candidate in stored data")
        values: dict[Label, Interval] = {}
        for branch, m, numerator in roots:
            a, b = Q(numerator, DEN), Q(numerator+1, DEN)
            context = f"h={hs}, t={t}, branch={branch}, m={m}"
            if branch == "light":
                require(0 < a < b < Q(1, m+1), "Light branch bounds: "+context)
                require(entropy_bounds(a, m)[1] < h < entropy_bounds(b, m)[0],
                        "Light entropy signs: "+context)
            else:
                require(branch == "heavy", "Unknown branch: "+context)
                require(Q(1, m+1) < a < b < 1, "Heavy branch bounds: "+context)
                require(entropy_bounds(b, m)[1] < h < entropy_bounds(a, m)[0],
                        "Heavy entropy signs: "+context)
            values[(branch, m)] = objective_bounds(a, b, m, t)
        winner = max(values, key=lambda label: values[label][0])
        require(winner == expected_winner, "Winner label mismatch: "+hs)
        require(all(values[winner][0] > interval[1]
                    for label, interval in values.items() if label != winner),
                "Strict optimality not certified: "+hs)
        results[(hs, t)] = values
        print(f"h={hs}, t={t}: unique winner {winner!r}")
        for label, interval in values.items():
            print(" ", label, decimal_interval(interval))

    values = results[("19/8", 8)]
    require(values[("heavy", 10)][0] > values[("heavy", 11)][1],
            "Nonunimodality: first comparison failed")
    require(values[("heavy", 12)][0] > values[("heavy", 11)][1],
            "Nonunimodality: second comparison failed")
    print("Certified: heavy-branch unimodality fails.")
    print("Certified: at t=3 and h=11/10, 6/5, 7/5 the unique types are light, heavy, light.")
    print("All exact rational certificates passed.")


if __name__ == "__main__":
    main()
