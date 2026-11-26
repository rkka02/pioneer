#!/usr/bin/env python3
"""Independent small-board checks and bounded runs for the final round."""
import argparse
from functools import lru_cache
import subprocess
import sys
import time

from research import WholeTurns


def run(args, **kwargs):
    return subprocess.check_output(list(map(str, args)), text=True, timeout=180, **kwargs)


def scalar_uniform(weights, flat_max):
    @lru_cache(None)
    def safe(mask, d, defender):
        if not mask:
            return not defender or d == 0
        rising = bin(mask).count("1") % 2
        live = [i for i in range(len(weights)) if mask >> i & 1]
        if defender and not rising and flat_max:
            live = live[-1:]
        def child(i):
            x = weights[i]
            return (rising or d <= x) and safe(mask ^ (1 << i), abs(d-x),
                                               defender if x < d else not defender)
        return (any if defender else all)(child(i) for i in live)
    return safe


def audit_uniform(binary, n):
    a = 2*n+1
    weights = tuple(range(a, a+2*n-1))
    shifts = [0, 3, 37]
    games = [WholeTurns([x+t for x in weights]) for t in shifts]
    for flat_max in (False, True):
        args = [binary, n, a, "--dump"] + (["--flat-max"] if flat_max else [])
        rows = run(args).splitlines()[1:]
        safe = scalar_uniform(weights, flat_max)
        for row in rows:
            mask, d, acts, waits = map(int, row.split())
            assert (safe(mask, d, True), safe(mask, d, False)) == (acts, waits), row
            rising = bin(mask).count("1") % 2
            for t, game in zip(shifts, games):
                margin = game.margin(mask, d+rising*t)
                assert (not acts or margin >= 0) and (not waits or margin <= 0), (row,t,margin)
        print("symbolic", "flat-max" if flat_max else "unrestricted", len(rows),
              "states, both roles, shifts", shifts, flush=True)
        safe.cache_clear()
    for game in games:
        game.close()


def audit_fixed(binary, n):
    game = WholeTurns(range(1, n+1))
    args = [binary,n,n//2,n,"--packed","--pair-cuts"]
    pairs = set()
    for line in run(args+["--split",3,*range(1,n+1)]).splitlines():
        _,a,b,side,holds = line.split()
        a,b = int(a),int(b)
        assert a != b and side == "P1" and (a,b) not in pairs
        pairs.add((a,b))
        board = game.full ^ (1<<(a-1)) ^ (1<<(b-1))
        margin = game.margin(board,abs(a-b)) * (1 if b>=a else -1)
        assert bool(int(holds)) == (margin>=0), (a,b,holds,margin)
    assert len(pairs) == n*(n-1)
    rows = run(args+["--offsets"]).splitlines()
    flat = game.margin(game.full^7,2)
    assert list(map(int,rows[0].split()[2:])) == [int(flat>=0),int(flat<=0)]
    for a in [2,3]:
        bad = [x for x in range(a+1,n+1)
               if game.margin(game.full ^ ((1<<(a-1))-1) ^ (3<<(x-2)),0)>0]
        assert list(map(int,rows[a-1].split()[3:])) == bad
    print("fixed player",len(pairs),"conditional openings and both hole families",flush=True)
    game.close()


def audit_adaptive(binary, n, free):
    game=WholeTurns(range(1,n+1))

    @lru_cache(None)
    def safe(board,d,me):
        total=game.total(board)
        if total<=d:
            return not me or total==d
        w=game.labels(board)
        if len(w)<=free:
            margin=game.margin(board,d)
            return margin>=0 if me else margin<=0
        if me and 2*w[-1]>=total+d:
            return True
        if not me and 2*w[-1]>total+d:
            return False
        moves=w
        if d:
            critical=(len(w)==2*d and w[-1]-w[0]+1==len(w))
            if critical and d<=8 and w[0]+1>=len(w):
                return True
            if critical and w[0]>=len(w)+1:
                if not me:
                    return True
                moves=(w[-1],)
            else:
                for bank_size in range(len(w)%2,len(w),2):
                    high=w[bank_size:]
                    spread=sum(v-u for u,v in zip(high[::2],high[1::2]))
                    reserve=sum(w[:bank_size])+spread
                    if high[1]>=d+spread and reserve<=d and (reserve<d or not me):
                        return not me
        if me:
            for u in w:
                v=d-u
                if u>=v or v not in w:
                    continue
                rest=board ^ (1<<(u-1)) ^ (1<<(v-1))
                if rest and 3*bin(rest).count("1")>2*rest.bit_length()+1 and safe(rest,0,False):
                    return True
            lower=[x for x in w if x<d]
            upper=[x for x in w if x>=d]
            allowed={w[0],w[-1],*(lower[-1:]),*(upper[:1])}
            moves=tuple(x for x in moves if x in allowed)
        return (any if me else all)(safe(board^(1<<(x-1)),abs(d-x),me if x<d else not me)
                                    for x in moves)

    rows=run([binary,n,0,n,"--pair-cuts","--adaptive",free,"--offsets"]).splitlines()
    assert list(map(int,rows[0].split()[2:])) == [safe(game.full^7,2,p) for p in (True,False)]
    for a in (2,3):
        bad=[x for x in range(a+1,n+1) if not safe(game.full^((1<<(a-1))-1)^(3<<(x-2)),0,False)]
        assert bad == list(map(int,rows[a-1].split()[3:]))
    print("adaptive boundary and hole families",n,"free endgame",free,flush=True)
    game.close()


def audit_layer(binary, n):
    game = WholeTurns(range(1,n+1))
    counts = [0]*6
    k=1
    while k*(k+1)//2<n:
        k+=1
    for s in range(1<<(n-1),1<<n):
        if game.total(s)%2:
            continue
        dense = 3*bin(s).count("1")>2*n+1
        bank = k<n and s & ((1<<k)-1) == (1<<k)-1
        if dense or bank:
            margin=game.margin(s,0)
            col=0 if margin>0 else 2 if margin<0 else 1
            counts[col]+=dense
            counts[col+3]+=bank
    for workers in (1,3):
        assert list(map(int,run([binary,n,workers]).split())) == [n,*counts]
    print("density and bank layer",n,counts,flush=True)
    game.close()


def critical_policy(n, restrict_rising):
    """Test a fixed-player policy after the forced maximum at height 2*n+1."""
    a = 2*n + 1

    @lru_cache(None)
    def holds(tokens, gap, defender):
        if not tokens:
            return not defender or gap == 0
        choices = tokens
        if defender and len(tokens) % 2 == 0:
            choices = tokens[-1:]
        elif defender and restrict_rising:
            below = [x for x in tokens if x < gap]
            above = [x for x in tokens if x >= gap]
            choices = sorted({tokens[0], tokens[-1], *below[-1:], *above[:1]})
        return (any if defender else all)(
            holds(tuple(y for y in tokens if y != x), abs(gap-x),
                  defender if x < gap else not defender)
            for x in choices)

    result = holds(tuple(range(a, a+2*n-1)), a+n-1, False)
    holds.cache_clear()
    return result


def offsets():
    for a in range(1,11):
        outcomes=[]
        for i in range(9):
            board = set(range(a,a+10))-{a+i,a+i+1}
            game = WholeTurns(board)
            outcomes.append(game.margin(game.full,0))
            game.close()
        assert outcomes == [0]*9
    print("90 ten-token interval deletions draw")
    game=WholeTurns([7,8,9,10,11,12])
    steps=[12,8,11,10,9,7]
    s=game.full
    d=3
    mine=True
    for x in steps:
        s^=1<<game.w.index(x)
        mine=mine if x<d else not mine
        d=abs(d-x)
    assert s==0 and (-d if mine else d)==-2
    game.close()
    for hole,expected in [((6,7),2),((7,8),0),((6,9),-2)]:
        game=WholeTurns(set(range(5,11))-set(hole))
        assert game.margin(game.full,2)==expected
        game.close()
    print("greedy refutation and all three two-hole outcomes verified")
    for n in range(1, 8):
        assert critical_policy(n, False)
        assert critical_policy(n, True) == (n <= 6)
    tokens = set(range(15, 29))
    gap, defender = 7, True
    for x in (28, 17, 18, 15, 23, 22, 26, 27, 25):
        tokens.remove(x)
        defender = defender if x < gap else not defender
        gap = abs(gap-x)
    assert defender and gap == 24 and tokens == {16, 19, 20, 21, 24}
    game = WholeTurns(tokens)
    assert game.picks(game.full, gap) == [(16,-4), (19,2), (20,-4), (21,-2), (24,-2)]
    game.close()
    print("At seven pairs the restricted high-interval policy fails. The five-token witness requires 19.")


def main():
    p=argparse.ArgumentParser(description=__doc__)
    commands=p.add_subparsers(dest="cmd",required=True)
    q=commands.add_parser("audit")
    for tool in ["uniform","defense","layer"]:
        q.add_argument(tool)
    commands.add_parser("examples")
    q=commands.add_parser("limit")
    q.add_argument("seconds",type=float)
    q.add_argument("program",nargs=argparse.REMAINDER)
    args=p.parse_args()
    if args.cmd=="audit":
        audit_uniform(args.uniform,5)
        audit_fixed(args.defense,12)
        audit_adaptive(args.defense,15,6)
        audit_layer(args.layer,12)
    elif args.cmd=="examples":
        offsets()
    else:
        if not args.program or not 0<args.seconds<600:
            p.error("supply a program and a deadline strictly below 600 seconds")
        t=time.monotonic()
        try:
            code=subprocess.run(args.program,timeout=args.seconds).returncode
        except subprocess.TimeoutExpired:
            print("Deadline reached.",file=sys.stderr)
            code=124
        print(f"Elapsed {time.monotonic()-t:.2f} seconds.",file=sys.stderr)
        raise SystemExit(code)


if __name__=="__main__":
    main()
