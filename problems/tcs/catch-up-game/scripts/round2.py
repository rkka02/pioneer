#!/usr/bin/env python3
"""Independent whole-turn audit of bounded handoffs and searches for consecutive-bank examples."""
import argparse
from functools import cache
from itertools import combinations
import random
import subprocess

from research import WholeTurns


def audit(binary, n):
    game = WholeTurns(range(1, n+1))
    cases = [(1,False,False,0,False), (2,False,False,0,False), (2,True,False,0,False),
             (1,False,True,0,False), (2,False,True,0,False), (2,True,True,0,False),
             (0,False,False,3,True), (0,False,False,4,True), (0,False,True,3,False)]
    for cap, isolated, exit_win, rank, all_ties in cases:
        @cache
        def safe(mask, d, defender, exact_next):
            margin = game.margin(mask,d)
            if not all_ties and not defender and d == 0 and margin:
                return False
            if exit_win and (margin > 0 if defender else margin < 0):
                return True
            if not mask or game.total(mask) < d:
                return (game.total(mask) >= d) if defender else True
            if defender:
                for take in game.turns(mask,d):
                    lead = game.total(take)-d
                    allowance = cap
                    if rank:
                        live = game.labels(mask^take)
                        allowance = live[rank-1] + cap if len(live)>=rank else n
                    if lead <= (0 if exact_next else allowance) and safe(mask^take,lead,False,isolated and lead>0):
                        return True
                return False
            return all(safe(mask^take,game.total(take)-d,True,exact_next) for take in game.turns(mask,d))

        args=[binary,str(n),str(cap),"--dump"]
        if isolated: args.append("--isolated")
        if exit_win: args.append("--winning-exit")
        if rank: args.extend(["--rank",str(rank)])
        if all_ties: args.append("--all-ties")
        checked=0
        for row in subprocess.check_output(args,text=True).splitlines():
            if not row.startswith("state "): continue
            mask,d,defend,oppose=map(int,row.split()[1:])
            assert bool(defend)==safe(mask,d,True,False),(args,mask,d,"defender")
            assert bool(oppose)==safe(mask,d,False,isolated and d>0),(args,mask,d,"opponent")
            checked+=1
        print(" ".join(args[1:]),checked,"positions, both roles",flush=True)
        safe.cache_clear()
    game.close()


def audit_threshold(binary, n):
    """Cross-check conditional openings and every reported minimum-ray obligation."""
    game=WholeTurns(range(1,n+1))
    if sum(game.w)%2 or n<4: raise ValueError("need an even-total prefix of size at least four")
    def label(v):
        return "W" if v>0 else "L" if v<0 else "D"
    options=[binary,"--small-first","--prefer-exact","--pair-cuts","--endgame",str(n//2),"--cache-bits","14"]
    for a in range(1,n+1):
        b0=n if a==1 else 1
        out=subprocess.check_output(options+["--opening",str(a),str(b0),str(n)],text=True)
        for line in out.splitlines():
            _,_,b,role,flag=line.split()
            b=int(b)
            m=game.full ^ (1<<(a-1)) ^ (1<<(b-1))
            p1=game.margin(m,abs(a-b)) * (1 if a<b else -1)
            assert int(flag)==(p1>=0 if role=="P1" else p1<=0),(a,b,role,flag,p1)
    rows=subprocess.check_output(options+["--ray","2",str(n),str(n)],text=True)
    for line in rows.splitlines():
        _,a,d,root,boundary,band,ties=line.split()
        a,d=int(a),int(d)
        s=game.full ^ ((1<<(a-1))-1)
        assert (root,boundary)==(label(game.margin(s,d)),label(game.margin(s^(1<<(a-1)),a-d)))
        losing_band=winning_ties=0
        for x in range(a+1,n+1):
            after=s^(1<<(x-1))
            if x<a+d: losing_band+=game.margin(after,x-d)<0
            else: winning_ties+=game.margin(after^(1<<(x-d-1)),0)>0
        assert (int(band),int(ties))==(losing_band,winning_ties)
    rows=subprocess.check_output(options+["--opening-range","1",str(n),str(n)],text=True).splitlines()
    assert len(rows)==n
    for row,(x,margin) in zip(rows,game.openings()):
        _,token,result=row.split()
        assert int(token)==x and (result=="holds")==(margin>=0)
    print(n,"all conditional openings and minimum-ray rows agree")
    rows=subprocess.check_output([binary,"--set","--roots","--small-first","--prefer-exact","--pair-cuts",
                                  "--cache-bits","16",*map(str,game.w)],text=True).strip()
    assert len(rows)==1<<n
    for m,v in enumerate(rows):
        assert v==label(game.margin(m,0)),(m,v)
    print(n,"all tied subset outcomes agree with the bank-and-pairs cutoff enabled")
    for d in range(n+1):
        row=subprocess.check_output(options+["--pick-values","--gap",str(d),str(n)],text=True).split()
        assert row[3]==label(game.margin(game.full,d))
        assert row[4]=="".join(label(value) for _,value in game.picks(game.full,d))
    print(n,"per-pick values agree at every initial deficit through the maximum")
    game.close()
    for pairs in range(1,7):
        for a in (2*pairs,2*pairs+1,2*pairs+2):
            weights=tuple(range(a,a+2*pairs))
            high=WholeTurns(weights)
            args=[binary,"--set","--small-first","--plain-ties","--pair-cuts","--pick-values",
                  "--gap",str(pairs),"--cache-bits","14",*map(str,weights)]
            row=subprocess.check_output(args,text=True).split()
            assert row[3]==label(high.margin(high.full,pairs))
            assert row[4]=="".join(label(v) for _,v in high.picks(high.full,pairs))
            high.close()
    print("18 high intervals agree, including both sides of the maximum-only theorem's cutoff")


def bank_test(binary, lo, hi, trials):
    rng=random.Random(204803)
    for k in range(lo,hi+1):
        bank=tuple(range(1,k+1))
        total=sum(bank)
        candidates=set()
        for q in range(1,min(9,total-k+1)):
            for top in range(max(k+q,total-17),total+1):
                for gap in range(0,q+1):
                    high=tuple(x for x in range(top-q,top+1) if x!=top-gap)
                    if high[0]>k and (total+sum(high))%2==0: candidates.add(bank+high)
            for _ in range(trials):
                high=tuple(sorted(rng.sample(range(k+1,total+1),q)))
                if (total+sum(high))%2==0: candidates.add(bank+high)
        items=sorted(candidates,key=lambda w:(len(w),w))
        counts={"W":0,"D":0,"L":0}
        for start in range(0,len(items),128):
            group=items[start:start+128]
            data="".join(" ".join(map(str,w))+"\n" for w in group)
            result=subprocess.check_output([binary,"--batch-sets","--small-first","--cache-bits","14"],input=data,text=True).splitlines()
            assert len(result)==len(group)
            for w,v in zip(group,result):
                if v!="D" and not counts[v]: print("witness",v,*w,flush=True)
                counts[v]+=1
        print("bank",k,"boards",len(items),counts,flush=True)


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    commands=parser.add_subparsers(dest="command",required=True)
    p=commands.add_parser("audit")
    p.add_argument("binary");p.add_argument("n",type=int)
    p=commands.add_parser("banks")
    p.add_argument("binary");p.add_argument("lo",type=int);p.add_argument("hi",type=int)
    p.add_argument("--trials",type=int,default=200)
    p=commands.add_parser("threshold")
    p.add_argument("binary");p.add_argument("n",type=int)
    args=parser.parse_args()
    if args.command=="audit": audit(args.binary,args.n)
    elif args.command=="threshold": audit_threshold(args.binary,args.n)
    else: bank_test(args.binary,args.lo,args.hi,args.trials)
