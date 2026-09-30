"""Numeric sanity check of Carnot's theorem with the signed-distance convention of
Carnot/Main.lean: signedSideDist i p = <p - F_i, A_i - F_i> / h_i (positive towards vertex i)."""
import random, math
def sub(p,q): return (p[0]-q[0],p[1]-q[1])
def dot(u,v): return u[0]*v[0]+u[1]*v[1]
def foot(p,q,r):  # foot of perpendicular from p to line qr
    d=sub(r,q); t=dot(sub(p,q),d)/dot(d,d); return (q[0]+t*d[0],q[1]+t*d[1])
def circ(A,B,C):
    ax,ay=A;bx,by=B;cx,cy=C; d=2*(ax*(by-cy)+bx*(cy-ay)+cx*(ay-by))
    ux=((ax*ax+ay*ay)*(by-cy)+(bx*bx+by*by)*(cy-ay)+(cx*cx+cy*cy)*(ay-by))/d
    uy=((ax*ax+ay*ay)*(cx-bx)+(bx*bx+by*by)*(ax-cx)+(cx*cx+cy*cy)*(bx-ax))/d
    return (ux,uy)
def ang(p,q,r):
    u,v=sub(p,q),sub(r,q); return math.acos(max(-1,min(1,dot(u,v)/math.sqrt(dot(u,u)*dot(v,v)))))
random.seed(1); worst=0; nobtuse=0
for _ in range(20000):
    P=[(random.uniform(-10,10),random.uniform(-10,10)) for _ in range(3)]
    area2=abs((P[1][0]-P[0][0])*(P[2][1]-P[0][1])-(P[2][0]-P[0][0])*(P[1][1]-P[0][1]))
    if area2<1e-2: continue
    O=circ(*P); R=math.dist(O,P[0])
    a,b,c=math.dist(P[1],P[2]),math.dist(P[0],P[2]),math.dist(P[0],P[1])
    r=area2/(a+b+c)
    ds=[]
    for i in range(3):
        j,k=[x for x in range(3) if x!=i]; F=foot(P[i],P[j],P[k]); h=math.dist(P[i],F)
        ds.append(dot(sub(O,F),sub(P[i],F))/h)
    A=[ang(P[1],P[0],P[2]),ang(P[0],P[1],P[2]),ang(P[0],P[2],P[1])]
    if max(A)>math.pi/2: nobtuse+=1; assert min(ds)<0
    e=max(abs(sum(ds)-(R+r))/R, abs(sum(map(math.cos,A))-(1+r/R)),
          max(abs(ds[i]-R*math.cos(A[i]))/R for i in range(3)))
    worst=max(worst,e)
print(f"triangles with obtuse angle: {nobtuse}; max relative error: {worst:.3e}")
assert worst<1e-8; print("OK")
