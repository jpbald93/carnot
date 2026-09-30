from certlib import *
w0=1-x-y
for nm,G in [('cosA', w0*b**2*c**2-R**2*(b**2+c**2-a**2)),
             ('cosB', x*a**2*c**2-R**2*(a**2+c**2-b**2)),
             ('cosC', y*a**2*b**2-R**2*(a**2+b**2-c**2))]:
  for deg in range(0,4):
    q=find(expand(G),[hx0,hx1,hx2],[a,b,c,x,y,R],deg)
    if q:
        print(nm,deg,' + '.join(f'({lean(ci)}) * {n}' for ci,n in zip(q,['hx0','hx1','hx2']) if ci!=0), flush=True); break
  else: print(nm,'none')
# sum cos identity: D*sum a(b^2+c^2-a^2) - 2abcD - 4 k^2 = q*hk
G=expand((a+b+c)*(a*(b**2+c**2-a**2)+b*(a**2+c**2-b**2)+c*(a**2+b**2-c**2))-2*a*b*c*(a+b+c)-4*k**2)
print('sumcos', factor(expand(G+4*hk)))
