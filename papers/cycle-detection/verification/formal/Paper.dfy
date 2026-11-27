include "Criterion.dfy"
module Paper {
  import opened Windows
  import opened Criterion
  // p is an integer prefix sum; its additive constant is immaterial.
  ghost predicate Binary(p:int->int,N:int,m:int) {
    (forall x:int :: 0<=p(x+1)-p(x)<=1) &&
    (forall x:int :: p(x+N)==p(x)+m)
  }
  ghost function C(p:int->int,x:int,l:int):int { p(x+l)-p(x) }
  ghost predicate Width(p:int->int,l:int) {
    forall x,y:int :: C(p,x,l)-C(p,y,l)<=1
  }
  ghost predicate Tests(p:int->int,L:seq<nat>) {
    forall i:int :: 0<=i<|L| ==> Width(p,L[i])
  }
  ghost predicate All(p:int->int,N:int) {
    forall l:int :: 1<=l<N ==> Width(p,l)
  }
  ghost predicate IsTestSet(N:int,m:int,L:seq<nat>) {
    forall p:int->int :: Binary(p,N,m) && Tests(p,L) ==> All(p,N)
  }
  ghost function Err(p:int->int,n:int,h:int):int->int { x => n*p(x)-h*x }
  ghost function D(e:int->int,x:int,l:int):int { e(x+l)-e(x) }
  lemma Delta(p:int->int,n:int,h:int,x:int,l:int)
    ensures D(Err(p,n,h),x,l)==n*C(p,x,l)-h*l
  {}
  lemma Encode(p:int->int,n:nat,h:nat,d:nat)
    requires 1<n && 0<h<n && d>0 && Binary(p,n*d,h*d)
    ensures Word(Err(p,n,h),n,h,n*d)
  {
    var e:=Err(p,n,h);
    forall x:int ensures e(x+n*d)==e(x) {
      assert p(x+n*d)==p(x)+h*d;
      calc { e(x+n*d); == n*(p(x)+h*d)-h*(x+n*d); == e(x); }
    }
    forall x:int ensures -n<D(e,x,1)<n {
      Delta(p,n,h,x,1);
      assert C(p,x,1)==0 || C(p,x,1)==1;
    }
    forall x:int ensures Cong(e(x),-h*x,n) { assert e(x)+h*x==p(x)*n; }
  }
  lemma Decode(e:int->int,n:nat,h:nat,d:nat) returns (p:int->int)
    requires 1<n && 0<h<n && d>0 && Word(e,n,h,n*d)
    ensures Binary(p,n*d,h*d) && Err(p,n,h)==e
  {
    p:=(x:int) => (e(x)+h*x)/n;
    forall x:int ensures n*p(x)-h*x==e(x) {
      var k :| e(x)+h*x==k*n; ModExact(e(x)+h*x,n,k,0);
    }
    assert forall x:int :: Err(p,n,h)(x)==e(x);
    assert Err(p,n,h)==e;
    forall x:int ensures 0<=C(p,x,1)<=1 {
      Delta(p,n,h,x,1);
      var k:=C(p,x,1);
      if k<0 { assert n*k<=-n; } else if k>1 { assert n*k>=2*n; }
    }
    forall x:int ensures p(x+n*d)==p(x)+h*d {
      Delta(p,n,h,x,n*d);
      assert e(x+n*d)==e(x);
      calc { n*C(p,x,n*d); == h*(n*d); == n*(h*d); }
    }
  }
  ghost function Sum(f:int->int,x:int,k:nat):int decreases k {
    if k==0 then 0 else f(x)+Sum(f,x+1,k-1)
  }
  lemma Slide(f:int->int,x:int,k:nat)
    ensures Sum(f,x+1,k)-Sum(f,x,k)==f(x+k)-f(x)
    decreases k
  { if k>0 { Slide(f,x+1,k-1); } }
  lemma SlideBy(e:int->int,N:nat,x:int,l:nat)
    requires Per(e,N)
    ensures Sum(e,x+l,N)==Sum(e,x,N)
    decreases l
  { if l>0 { SlideBy(e,N,x,l-1); Slide(e,x+l-1,N); } }
  lemma SumDiff(e:int->int,x:int,k:nat,l:int)
    ensures Sum(y=>D(e,y,l),x,k)==Sum(e,x+l,k)-Sum(e,x,k)
    decreases k
  { if k>0 { SumDiff(e,x+1,k-1,l); } }
  lemma SumSign(f:int->int,x:int,k:nat)
    requires (forall y:int :: f(y)>=0) || (forall y:int :: f(y)<=0)
    ensures (forall y:int :: f(y)>=0) ==> Sum(f,x,k)>=0
    ensures (forall y:int :: f(y)<=0) ==> Sum(f,x,k)<=0
    decreases k
  { if k>0 { SumSign(f,x+1,k-1); } }
  lemma MeanZero(e:int->int,N:nat,x:int,l:nat)
    requires Per(e,N)
    ensures Sum(y=>D(e,y,l),x,N)==0
  { SlideBy(e,N,x,l); SumDiff(e,x,N,l); }
  lemma {:isolate_assertions} WidthGood(p:int->int,n:nat,h:nat,N:nat,l:nat)
    requires n>1 && N>0 && Per(Err(p,n,h),N)
    ensures Width(p,l) <==> Good(Err(p,n,h),n,l)
  {
    var e:=Err(p,n,h); var f:=(y:int)=>D(e,y,l);
    if Width(p,l) {
      forall x:int ensures -n<f(x)<n {
        Delta(p,n,h,x,l);
        if f(x)>=n || f(x)<=-n {
          forall y:int ensures (f(x)>=n ==> f(y)>=0) && (f(x)<=-n ==> f(y)<=0) {
            Delta(p,n,h,y,l);
            assert -1<=C(p,y,l)-C(p,x,l)<=1;
            assert -n<=n*(C(p,y,l)-C(p,x,l))<=n;
            assert f(y)-f(x)==n*(C(p,y,l)-C(p,x,l));
          }
          SumSign(f,x+1,N-1); MeanZero(e,N,x,l);
          assert Sum(f,x,N)==f(x)+Sum(f,x+1,N-1);
        }
      }
    } else if Good(e,n,l) {
      forall x,y:int ensures C(p,x,l)-C(p,y,l)<=1 {
        Delta(p,n,h,x,l); Delta(p,n,h,y,l);
        if C(p,x,l)-C(p,y,l)>=2 {
          assert n*(C(p,x,l)-C(p,y,l))>=2*n;
          assert f(x)-f(y)==n*(C(p,x,l)-C(p,y,l));
        }
      }
    }
  }
  lemma Translate(p:int->int,n:nat,h:nat,N:nat,L:seq<nat>)
    requires n>1 && N>0 && Per(Err(p,n,h),N)
    ensures Tests(p,L) <==> Pass(Err(p,n,h),n,L)
    ensures All(p,N) <==> Balanced(Err(p,n,h),n,N)
  {
    forall i:int | 0<=i<|L| ensures Width(p,L[i]) <==> Good(Err(p,n,h),n,L[i]) {
      WidthGood(p,n,h,N,L[i]);
    }
    forall l:int | 1<=l<N ensures Width(p,l) <==> Good(Err(p,n,h),n,l) {
      WidthGood(p,n,h,N,l);
    }
  }
  lemma Main(n:nat,h:nat,d:nat,L:seq<nat>)
    requires 1<n && 0<h<n && d>0 && Gcd(h,n)==1
    ensures IsTestSet(n*d,h*d,L) <==> (FilterG(n,n*d,L)==n && Shape(n,h,L))
  {
    var N:=n*d; ModExact(N,n,d,0);
    assert n<=N;
    WindowCriterion(n,h,N,L);
    if Decides(n,h,N,L) {
      forall p:int->int | Binary(p,N,h*d) && Tests(p,L) ensures All(p,N) {
        Encode(p,n,h,d); Translate(p,n,h,N,L);
      }
    } else {
      var e :| Word(e,n,h,N) && Pass(e,n,L) && !Balanced(e,n,N);
      var p:=Decode(e,n,h,d); Translate(p,n,h,N,L);
      assert !IsTestSet(N,h*d,L);
    }
  }
}
