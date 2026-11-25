#!/usr/bin/env python3
"""Whole-turn minimax, independent cross-checks, strategy tests and subset census."""
import argparse
import subprocess
from collections import Counter, deque
from functools import cache
from itertools import combinations


def sign(value):
    return "W" if value > 0 else "L" if value < 0 else "D"


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit
        mask ^= bit


class WholeTurns:
    def __init__(self, weights):
        self.w = tuple(sorted(weights))
        if any(x < 0 for x in self.w):
            raise ValueError("weights must be nonnegative")
        self.full = (1 << len(self.w)) - 1

    def weight(self, bit):
        return self.w[bit.bit_length() - 1]

    def labels(self, mask):
        return tuple(self.weight(bit) for bit in bits(mask))

    @cache
    def total(self, mask):
        if not mask:
            return 0
        bit = mask & -mask
        return self.weight(bit) + self.total(mask ^ bit)

    def turns(self, mask, gap):
        """Enumerate each legal turn-set once, placing its largest element last."""
        if gap == 0:
            yield from bits(mask)
            return

        def extend(available, taken, missing):
            while available:
                bit = available & -available
                available ^= bit
                x = self.weight(bit)
                if x >= missing:
                    yield taken | bit
                else:
                    yield from extend(available, taken | bit, missing - x)

        yield from extend(mask, 0, gap)

    @cache
    def margin(self, mask, gap):
        total = self.total(mask)
        if total <= gap:
            return total - gap
        return max(-self.margin(mask ^ take, self.total(take) - gap)
                   for take in self.turns(mask, gap))

    def picks(self, mask, gap):
        values = []
        for bit in bits(mask):
            x = self.weight(bit)
            value = self.margin(mask ^ bit, gap-x) if x < gap else -self.margin(mask ^ bit, x-gap)
            values.append((x, value))
        return values

    def openings(self):
        return [(self.weight(bit), -self.margin(self.full ^ bit, self.weight(bit)))
                for bit in bits(self.full)]

    def forced_equality(self):
        """Which openings let each designated player force an exact final tie?"""
        @cache
        def play(mask, gap, defender_acts):
            total = self.total(mask)
            if total <= gap:
                return total == gap
            children = (play(mask ^ take, self.total(take) - gap, not defender_acts)
                        for take in self.turns(mask, gap))
            return any(children) if defender_acts else all(children)

        p1 = [self.weight(bit) for bit in bits(self.full)
              if play(self.full ^ bit, self.weight(bit), False)]
        p2 = [self.weight(bit) for bit in bits(self.full)
              if play(self.full ^ bit, self.weight(bit), True)]
        play.cache_clear()
        return p1, p2

    def constrained(self, defender, rule):
        """Absolute P1 minimax margin; the defender gets an unrestricted opening."""
        @cache
        def play(mask, gap, player, first):
            if self.total(mask) <= gap:
                margin = self.total(mask) - gap
                return margin if player == 1 else -margin
            turns = list(self.turns(mask, gap))
            if player == defender and not first:
                if rule == "overshoot":
                    cheapest = min(map(self.total, turns))
                    turns = [t for t in turns if self.total(t) == cheapest]
                elif rule == "exact-turn":
                    turns = [t for t in turns if self.total(t) == gap] or turns
                elif rule == "exact-token":
                    turns = [t for t in turns if not (t & (t-1)) and self.total(t) == gap] or turns
                else:
                    remaining, taken = mask, 0
                    while remaining:
                        bit = remaining & -remaining if rule == "smallest" else 1 << (remaining.bit_length()-1)
                        taken |= bit
                        remaining ^= bit
                        if self.total(taken) >= gap:
                            break
                    turns = [taken]
            margins = (play(mask ^ t, self.total(t) - gap, 3 - player, False) for t in turns)
            return (max if player == 1 else min)(margins)
        value = play(self.full, 0, 1, True)
        play.cache_clear()
        return value if defender == 1 else -value

    def opening_graph(self):
        if len(set(self.w)) != len(self.w) or len(self.w) < 2:
            raise ValueError("the opening graph requires at least two distinct tokens")
        vertices = list(bits(self.full))
        beaten = {a: [] for a in vertices}
        incoming = {a: [] for a in vertices}
        for a, b in combinations(vertices, 2):
            margin = self.margin(self.full ^ a ^ b, self.weight(b) - self.weight(a))
            if margin:
                winner, loser = (a, b) if margin > 0 else (b, a)
                beaten[winner].append(loser)
                incoming[loser].append(winner)
        universal = any(len(others) == len(vertices)-1 for others in beaten.values())
        result = "W" if universal else "L" if all(incoming.values()) else "D"
        assert result == sign(self.margin(self.full, 0))
        return result, {self.weight(a): sorted(self.weight(b) for b in others)
                        for a, others in incoming.items()}

    def mirror(self, defender, adjacent=False):
        n = len(self.w)
        if self.w != tuple(range(1, n+1)):
            raise ValueError("mate test requires a prefix")
        if adjacent and n % 2:
            raise ValueError("adjacent pairs require an even number of tokens")

        @cache
        def play(mask, gap, defending, mate):
            if self.total(mask) <= gap:
                return self.total(mask) - gap
            options = mask & mate or mask
            outcomes = []
            for bit in bits(options):
                x = self.weight(bit)
                if x < gap:
                    outcomes.append(play(mask ^ bit, gap-x, defending, 0))
                else:
                    # Only the first pick of a defender's turn can be prescribed.
                    partner = (x+1 if x % 2 else x-1) if adjacent else n+1-x
                    next_mate = 0 if defending else 1 << (partner-1)
                    outcomes.append(-play(mask ^ bit, x-gap, not defending, next_mate))
            return max(outcomes)
        margin = play(self.full, 0, defender == 1, 0)
        play.cache_clear()
        return margin if defender == 1 else -margin

    def close(self):
        self.total.cache_clear()
        self.margin.cache_clear()


def get_rows(binary, n):
    out = subprocess.check_output([binary, str(n), "--dump"], text=True)
    rows = []
    for line in out.splitlines():
        mask, row = line.split()
        assert int(mask) == len(rows) and len(row) == n + 1
        rows.append(row)
    assert len(rows) == 1 << n
    return rows


def audit(binary, n):
    rows = get_rows(binary, n)
    game = WholeTurns(range(1, n + 1))
    for mask, row in enumerate(rows):
        for d, v in enumerate(row):
            actual = sign(game.margin(mask, d))
            if actual != v:
                raise AssertionError((game.labels(mask), d, v, actual))
    print(f"Full agreement on {len(rows) * (n+1):,} board/deficit pairs.")
    game.close()


def census(binary, n):
    rows = get_rows(binary, n)
    counts = Counter()
    witnesses = {}
    for mask, row in enumerate(rows):
        weights = tuple(bit.bit_length() for bit in bits(mask))
        total = sum(weights)
        if total % 2:
            continue
        reachable = 1
        for x in weights:
            reachable |= reachable << x
        partitionable = bool((reachable >> (total // 2)) & 1)
        key = (len(weights), partitionable, row[0])
        counts[key] += 1
        witnesses.setdefault(key, weights)
        if row[0] == "D" and not partitionable:
            raise AssertionError(weights)
    print("size  unpartitionable W/D/L  partitionable W/D/L")
    for k in range(n + 1):
        print(k, *["/".join(str(counts[k, p, v]) for v in "WDL") for p in (False, True)])
    print("total", *["/".join(str(sum(counts[k, p, v] for k in range(n+1))) for v in "WDL")
                      for p in (False, True)])
    for v in "WL":
        for p in (False, True):
            matches = [s for (k, q, o), s in witnesses.items() if q == p and o == v]
            if matches:
                print("minimum by cardinality, then mask", v, p, min(matches, key=lambda s: (len(s), s[::-1])))


def dense_intervals(binary, lo, hi):
    """Boards just above 3|S|=2 max(S)+1 with a short low interval and one possible high hole."""
    if not 3 <= lo <= hi <= 52:
        raise ValueError("use maximum weights in 3..52")
    masks = set()
    for n in range(lo, hi+1):
        size = (2*n+1)//3+1
        for low_count in range(7):
            for holes in (0, 1):
                first_high = n - (size-low_count+holes) + 1
                if first_high <= low_count+1 or first_high > n:
                    continue
                base = ((1 << low_count)-1) | (((1 << (n-first_high+1))-1) << (first_high-1))
                for deleted in range(first_high, n) if holes else (0,):
                    mask = base ^ (1 << (deleted-1)) if deleted else base
                    if sum(b.bit_length() for b in bits(mask)) % 2 == 0:
                        masks.add(mask)
    ordered = sorted(masks)
    raw = subprocess.check_output([binary, "--masks", "--small-first", "--endgame", str(min(22,hi)),
                                   "--cache-bits", "24", str(hi)],
                                  input="".join(f"{m}\n" for m in ordered), text=True)
    answers = {}
    for line in raw.splitlines():
        mask, outcome = line.split()
        answers[int(mask)] = outcome
    assert set(answers) == masks
    for n in range(lo, hi+1):
        counts = Counter(v for m, v in answers.items() if m.bit_length() == n)
        print(n, "W/D/L", *(counts[v] for v in "WDL"))
    for mask, value in answers.items():
        if value != "D":
            print("decisive", value, [b.bit_length() for b in bits(mask)])


def study(binary, n):
    rows = get_rows(binary, n)
    for k in (3, 4, 7, 8, 11, 12, 15, 16, 19, 20):
        if k > n:
            continue
        m, d, pv = (1 << k)-1, 0, []
        pair = Counter(rows[m ^ (1 << (a-1)) ^ (1 << (b-1))][b-a]
                       for a, b in combinations(range(1, k+1), 2))
        while m:
            v = rows[m][d]
            for bit in bits(m):
                x = bit.bit_length()
                child = rows[m ^ bit][abs(d-x)]
                from_mover = child if x < d else {"W":"L", "L":"W", "D":"D"}[child]
                if from_mover == v:
                    pv.append(x)
                    m ^= bit
                    d = abs(d-x)
                    break
            else:
                raise AssertionError("no optimal pick")
        print(k, "upper pair W/D/L", *(pair[v] for v in "WDL"), "optimal picks", *pv)

    for k in (4, 8, 12):
        if k > n:
            continue
        game = WholeTurns(range(1, k+1))
        for rule in ("smallest", "largest", "overshoot", "exact-turn", "exact-token"):
            print(k, rule, "guaranteed margins for P1 and P2",
                  *(game.constrained(player, rule) for player in (1, 2)))
        print(k, "complement when available, P1 and P2", *(game.mirror(i) for i in (1, 2)))
        print(k, "adjacent mate when available, P1 and P2", *(game.mirror(i, True) for i in (1, 2)))
        game.close()

    # A reachable nonterminal draw which ceases to draw after adding the next quartet.
    for k in (3, 4, 7, 8):
        if k + 4 > n:
            continue
        suffix = 15 << k
        q = deque([((1 << k)-1, 0, ())])
        seen = set()
        while q:
            mask, d, history = q.popleft()
            if (mask, d) in seen:
                continue
            seen.add((mask, d))
            if not mask or sum(b.bit_length() for b in bits(mask)) < d:
                continue
            if rows[mask][d] == "D" and rows[mask | suffix][d] != "D":
                print("append-four obstruction", k, history, "gap", d, "D ->", rows[mask | suffix][d])
                break
            for bit in bits(mask):
                x = bit.bit_length()
                q.append((mask ^ bit, abs(d-x), history+(x,)))

    for weights in [(4,5,6,7,8), (4,5,6,7,12,14), (3,6,7,9,10,13), (2,4,6,7,9,10)]:
        game = WholeTurns(weights)
        print(weights, "openings and margins", game.openings(), "incoming", game.opening_graph()[1])
        game.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)
    for name, default in [("audit", 12), ("census", 16), ("study", 12)]:
        p = sub.add_parser(name)
        p.add_argument("binary", help="path to compiled retrograde.cpp")
        p.add_argument("n", type=int, nargs="?", default=default)
    p = sub.add_parser("compare-roots", help="compare the complete W/D/L census across two engines")
    p.add_argument("retrograde")
    p.add_argument("threshold")
    p.add_argument("n", type=int)
    p = sub.add_parser("set", help="arbitrary token values; repetitions denote distinct copies")
    p.add_argument("weights", type=int, nargs="*")
    p = sub.add_parser("position", help="inspect exact margins for every next pick at a given deficit")
    p.add_argument("gap", type=int)
    p.add_argument("weights", type=int, nargs="*")
    p = sub.add_parser("graph", help="compute the directed first-pair graph on a distinct set")
    p.add_argument("weights", type=int, nargs="+")
    p = sub.add_parser("equality", help="find openings from which each player can force equal scores")
    p.add_argument("sizes", type=int, nargs="+")
    p = sub.add_parser("density", help="test dense unions of two intervals with one possible high hole")
    p.add_argument("binary", help="path to compiled threshold.cpp")
    p.add_argument("lo", type=int)
    p.add_argument("hi", type=int)
    args = parser.parse_args()
    if args.cmd == "compare-roots":
        rows = get_rows(args.retrograde, args.n)
        out = subprocess.check_output([args.threshold, "--roots", "--small-first", "--cache-bits", "24",
                                       str(args.n)], text=True).strip()
        assert out == "".join(row[0] for row in rows)
        print(f"All {len(out):,} subset roots agree.")
    elif args.cmd == "density":
        dense_intervals(args.binary, args.lo, args.hi)
    elif args.cmd == "equality":
        for n in args.sizes:
            if n < 1:
                parser.error("opening tests require a nonempty prefix")
            game = WholeTurns(range(1, n+1))
            p1, p2 = game.forced_equality()
            print(n, "P1", p1, "P2", p2, flush=True)
            game.close()
    elif args.cmd == "position":
        if args.gap < 0:
            parser.error("the deficit must be nonnegative")
        game = WholeTurns(args.weights)
        print("minimax margin", game.margin(game.full, args.gap))
        if game.full and game.total(game.full) >= args.gap:
            print("next picks and margins", game.picks(game.full, args.gap))
    elif args.cmd == "graph":
        result, incoming = WholeTurns(args.weights).opening_graph()
        print("value", result, "strictly defeating replies by opening", incoming)
    elif args.cmd == "set":
        game = WholeTurns(args.weights)
        print("minimax margin", game.margin(game.full, 0), "openings", game.openings())
    else:
        {"audit": audit, "census": census, "study": study}[args.cmd](args.binary, args.n)


if __name__ == "__main__":
    main()
