include "Windows.dfy"
module Criterion {
  import opened Windows
  lemma Trans(a:int,b:int,c:int)
    requires b>0 && c>0 && a%b==0 && b%c==0
    ensures a%c==0
  {
    var k:=a/b; var j:=b/c;
    assert a==k*b && b==j*c;
    assert a==(k*j)*c;
    ModExact(a,c,k*j,0);
  }
  lemma Common(a:nat,b:nat,n:nat)
    requires n>0 && a%n==0 && b%n==0
    ensures Gcd(a,b)%n==0
  {
    var u,v:=Bezout(a,b);
    var i:=a/n; var j:=b/n;
    assert a==i*n && b==j*n;
    calc { Gcd(a,b); == u*(i*n)+v*(j*n); == (u*i+v*j)*n; }
    ModExact(Gcd(a,b),n,u*i+v*j,0);
  }
  lemma FilterFacts(n:nat,N:nat,L:seq<nat>)
    requires n>1 && N>0 && N%n==0
    ensures var g:=FilterG(n,N,L); g>0 && g%n==0 && N%g==0
    ensures forall i:int :: 0<=i<|L| && L[i]%n==0 ==> L[i]%FilterG(n,N,L)==0
    decreases |L|
  {
    if |L|==0 { ModExact(N,N,1,0); }
    else {
      var last:=|L|-1; var pre:=L[..last];
      FilterFacts(n,N,pre);
      var a:=FilterG(n,N,pre); var b:=L[last]; var g:=FilterG(n,N,L);
      if b%n==0 {
        GcdFactors(a,b); Common(a,b,n); Trans(N,a,g);
      } else { ModExact(a,g,1,0); }
      forall i:int | 0<=i<|L| && L[i]%n==0 ensures L[i]%g==0 {
        if i<last { assert pre[i]==L[i]; Trans(L[i],a,g); }
      }
    }
  }
  function Phase(n:int,h:int,x:int):int requires n>0 { (h*x)%n }
  lemma AtPhase(n:nat,h:nat,z:int) returns (x:int)
    requires n>1 && Gcd(h,n)==1 && 0<=z<n
    ensures Phase(n,h,x)==z
  {
    var u,v:=Bezout(h,n); x:=z*u;
    calc { h*x; == z*(u*h); == z*(1-v*n); == (-z*v)*n+z; }
    ModExact(h*x,n,-z*v,z);
  }
  lemma ZeroPhase(n:nat,h:nat,l:int)
    requires n>1 && Gcd(h,n)==1 && Phase(n,h,l)==0
    ensures l%n==0
  {
    var u,v:=Bezout(h,n); var k:=(h*l)/n;
    assert h*l==k*n;
    calc { l; == l*(u*h+v*n); == u*(h*l)+(v*l)*n; == (u*k+v*l)*n; }
    ModExact(l,n,u*k+v*l,0);
  }
  lemma AddPhase(n:int,h:int,x:int,l:int)
    requires n>1
    ensures var a:=Phase(n,h,x)+Phase(n,h,l);
      Phase(n,h,x+l)==(if a<n then a else a-n)
  {
    var a:=Phase(n,h,x)+Phase(n,h,l);
    var t:=h*x/n+h*l/n;
    assert h*(x+l)==t*n+a;
    if a<n { ModExact(h*(x+l),n,t,a); }
    else { ModExact(h*(x+l),n,t+1,a-n); }
  }
  lemma MultPhase(n:int,h:int,l:int)
    requires n>0 && l%n==0
    ensures Phase(n,h,l)==0
  {
    assert l==(l/n)*n;
    assert h*l==(h*(l/n))*n;
    ModExact(h*l,n,h*(l/n),0);
  }
  ghost function Lift(n:int,h:int,u:int->bool):int->int requires n>1 {
    x => -Phase(n,h,x)+(if u(x) then n else 0)
  }
  lemma LiftClass(n:int,h:int,u:int->bool,x:int)
    requires n>1
    ensures Cong(Lift(n,h,u)(x),-h*x,n)
  {
    var k:=(h*x)/n+(if u(x) then 1 else 0);
    assert Lift(n,h,u)(x)+h*x==k*n;
  }
  lemma LiftGood(n:int,h:int,z:int,u:int->bool,l:int)
    requires n>1 && (forall x:int :: u(x) ==> Phase(n,h,x)==z)
    requires var r:=Phase(n,h,l);
      if r==0 then (forall x:int :: u(x+l)==u(x)) else r<=z && n-r<=z
    ensures Good(Lift(n,h,u),n,l)
  {
    forall x:int ensures -n<Lift(n,h,u)(x+l)-Lift(n,h,u)(x)<n {
      AddPhase(n,h,x,l);
      if u(x) { assert Phase(n,h,x)==z; }
      if u(x+l) { assert Phase(n,h,x+l)==z; }
    }
  }
  lemma {:isolate_assertions} LiftWord(n:nat,h:nat,N:nat,z:int,u:int->bool)
    requires n>1 && 0<h<n && N%n==0
    requires (forall x:int :: u(x) ==> Phase(n,h,x)==z)
    requires forall x:int :: u(x+N)==u(x)
    requires h<=z && n-h<=z
    ensures Word(Lift(n,h,u),n,h,N)
  {
    MultPhase(n,h,N); ModExact(h,n,0,h);
    LiftGood(n,h,z,u,1);
    forall x:int ensures Lift(n,h,u)(x+N)==Lift(n,h,u)(x) { AddPhase(n,h,x,N); }
    forall x:int ensures Cong(Lift(n,h,u)(x),-h*x,n) { LiftClass(n,h,u,x); }
  }
  lemma RemShift(x:int,l:int,g:int)
    requires g>0 && l%g==0
    ensures (x+l)%g==x%g
  {
    ModExact(x+l,g,x/g+l/g,x%g);
  }
  lemma {:isolate_assertions} PeriodWitness(n:nat,h:nat,N:nat,L:seq<nat>) returns (e:int->int)
    requires 1<n<=N && 0<h<n && N%n==0 && Gcd(h,n)==1
    requires FilterG(n,N,L)!=n
    ensures Word(e,n,h,N) && Pass(e,n,L) && !Balanced(e,n,N)
  {
    FilterFacts(n,N,L); var g:=FilterG(n,N,L);
    assert g>=n by { if g<n { ModExact(g,n,0,g); } }
    assert N>=g by { if N<g { ModExact(N,g,0,N); } }
    var y:=AtPhase(n,h,n-1);
    var u:= (x:int) => (x-y)%g==0;
    forall x:int | u(x) ensures Phase(n,h,x)==n-1 {
      Trans(x-y,g,n); MultPhase(n,h,x-y); AddPhase(n,h,y,x-y);
    }
    forall x:int ensures u(x+N)==u(x) { RemShift(x-y,N,g); }
    LiftWord(n,h,N,n-1,u);
    e:=Lift(n,h,u);
    forall i:int | 0<=i<|L| ensures Good(e,n,L[i]) {
      var l:=L[i];
      if Phase(n,h,l)==0 {
        ZeroPhase(n,h,l);
        forall x:int ensures u(x+l)==u(x) { RemShift(x-y,l,g); }
      }
      LiftGood(n,h,n-1,u,l);
    }
    ModExact(0,g,0,0); ModExact(n,g,0,n);
    ModExact(n,n,1,0); MultPhase(n,h,n); AddPhase(n,h,y,n);
    assert e(y+n)-e(y)==-n;
    assert !Good(e,n,n);
  }
  lemma {:isolate_assertions} ShapeWitness(n:nat,h:nat,N:nat,L:seq<nat>) returns (e:int->int)
    requires 1<n<=N && 0<h<n && N%n==0 && Gcd(h,n)==1
    requires !Shape(n,h,L)
    ensures Word(e,n,h,N) && Pass(e,n,L) && !Balanced(e,n,N)
  {
    var z:=n-2; var u:=(x:int) => Phase(n,h,x)==z;
    MultPhase(n,h,N);
    forall x:int ensures u(x+N)==u(x) { AddPhase(n,h,x,N); }
    LiftWord(n,h,N,z,u); e:=Lift(n,h,u);
    forall i:int | 0<=i<|L| ensures Good(e,n,L[i]) {
      var l:=L[i]; var r:=Phase(n,h,l);
      assert r!=1 && r!=n-1;
      if r==0 {
        forall x:int ensures u(x+l)==u(x) { AddPhase(n,h,x,l); }
      }
      LiftGood(n,h,z,u,l);
    }
    var y:=AtPhase(n,h,z); var t:=AtPhase(n,h,1); var s:=t%n;
    var k:=t/n;
    assert t==k*n+s;
    assert h*t-h*s==(h*k)*n;
    assert Cong(h*t,h*s,n); ScaleCong(h*t,h*s,n);
    if s==0 { ModExact(0,n,0,0); }
    AddPhase(n,h,y,s);
    assert e(y+s)-e(y)==-n-1;
    assert !Good(e,n,s);
  }
  lemma WindowCriterion(n:nat,h:nat,N:nat,L:seq<nat>)
    requires 1<n<=N && 0<h<n && N%n==0 && Gcd(h,n)==1
    ensures Decides(n,h,N,L) <==> (FilterG(n,N,L)==n && Shape(n,h,L))
  {
    if FilterG(n,N,L)!=n { var e:=PeriodWitness(n,h,N,L); }
    else if !Shape(n,h,L) { var e:=ShapeWitness(n,h,N,L); }
    else {
      forall e:int->int | Word(e,n,h,N) && Pass(e,n,L) ensures Balanced(e,n,N) {
        Sufficient(e,n,h,N,L);
      }
    }
  }
}
