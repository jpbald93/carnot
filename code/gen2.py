from certlib import *
S=(1-x-y)*b*c+x*a*c+y*a*b
D=a+b+c
G=expand(S*D-2*R**2*D-a*b*c)
# first check truth numerically-symbolically: solve x,y
sol=solve([hx1-hx0,hx2-hx0],[x,y],dict=True)[0]
R2=simplify((R**2-hx0).subs(sol))
print('check', simplify((S*D-2*R2*D-a*b*c).subs(sol)))
for deg in range(0,4):
    q=find(G,[hx0,hx1,hx2],[a,b,c,x,y,R],deg)
    print('deg',deg, q is not None, flush=True)
    if q:
        print(' + '.join(f'({lean(ci)}) * {n}' for ci,n in zip(q,['hx0','hx1','hx2']) if ci!=0)); break
