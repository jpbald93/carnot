"""Shared helpers: search for linear_combination certificates. Hyp `lhs = rhs` contributes (lhs - rhs)."""
from sympy import *
from itertools import combinations_with_replacement
a,b,c,x,y,R,k,T=symbols('a b c x y R k T')
w=(b**2+c**2-a**2)/2
Q=lambda p,q: p**2*c**2+2*p*q*w+q**2*b**2
heron=(2*a**2*b**2+2*b**2*c**2+2*c**2*a**2-a**4-b**4-c**4)/4
hx0=R**2-Q(0-x,0-y); hx1=R**2-Q(1-x,0-y); hx2=R**2-Q(0-x,1-y)
hk=k**2-heron; hRk=2*k*R-a*b*c
def find(goal, hyps, vars_, deg):
    mons=[Integer(1)]
    for d in range(1,deg+1):
        for cc in combinations_with_replacement(vars_,d): mons.append(Mul(*cc))
    unknowns=[]; total=0; qs=[]
    for i,h in enumerate(hyps):
        cs=symbols(f'q{i}_0:{len(mons)}'); unknowns+=cs
        q=sum(ci*m for ci,m in zip(cs,mons)); qs.append(q); total+=q*h
    sol=linsolve(Poly(expand(goal-total),*vars_).coeffs(),unknowns)
    if not sol: return None
    s=list(sol)[0]; sub=dict(zip(unknowns,s))
    res=[expand(q.subs(sub).subs({u:0 for u in unknowns})) for q in qs]
    assert expand(goal-sum(r*h for r,h in zip(res,hyps)))==0
    return res
def lean(e): return str(factor(e)).replace('**','^')
