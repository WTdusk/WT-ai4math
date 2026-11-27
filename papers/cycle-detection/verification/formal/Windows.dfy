// Dafny 4.11.0. Integer functions below are ghost mathematical objects.
module Windows {
  ghost predicate Per(e:int->int, p:int) { forall x:int :: e(x+p)==e(x) }
  ghost predicate Good(e:int->int,n:int,l:int) {
    forall x:int :: -n < e(x+l)-e(x) < n
  }
  ghost predicate Cong(a:int,b:int,n:int) { exists q:int :: a-b==q*n }
  ghost predicate Word(e:int->int,n:int,h:int,N:int) {
    Per(e,N) && Good(e,n,1) && (forall x:int :: Cong(e(x),-h*x,n))
  }
  ghost predicate Pass(e:int->int,n:int,L:seq<nat>) {
    forall i:int :: 0<=i<|L| ==> Good(e,n,L[i])
  }
  ghost predicate Balanced(e:int->int,n:int,N:int) {
    forall l:int :: 1<=l<N ==> Good(e,n,l)
  }
  ghost predicate Decides(n:int,h:int,N:int,L:seq<nat>) {
    forall e:int->int :: Word(e,n,h,N) && Pass(e,n,L) ==> Balanced(e,n,N)
  }
  function Gcd(a:nat,b:nat):nat decreases b {
    if b==0 then a else Gcd(b,a%b)
  }
  lemma Bezout(a:nat,b:nat) returns (u:int,v:int)
    ensures u*a+v*b==Gcd(a,b)
    decreases b
  {
    if b==0 { u,v:=1,0; }
    else {
      var s,t:=Bezout(b,a%b);
      u,v:=t,s-t*(a/b);
      assert a==(a/b)*b+a%b;
      calc { u*a+v*b; == t*(a-(a/b)*b)+s*b; == Gcd(a,b); }
    }
  }
  lemma {:isolate_assertions} ModExact(a:int,b:int,q:int,r:int)
    requires b>0 && 0<=r<b && a==q*b+r
    ensures a%b==r && a/b==q
  {
    var t:=a/b; var v:=a%b;
    assert a==t*b+v;
    calc { (q-t)*b; == q*b-t*b; == v-r; }
    if q>t { assert (q-t)*b>=b; } else if q<t { assert (q-t)*b<=-b; }
    assert q==t;
    assert v==r;
  }
  lemma ScaleCong(a:int,b:int,n:int) requires n>0 && Cong(a,b,n)
    ensures a%n==b%n
  {
    var q :| a-b==q*n;
    ModExact(a,n,q+b/n,b%n);
  }
  lemma GcdFactors(a:nat,b:nat)
    ensures Gcd(a,b)==0 ==> a==0 && b==0
    ensures Gcd(a,b)>0 ==> a%Gcd(a,b)==0 && b%Gcd(a,b)==0
    decreases b
  {
    if b!=0 {
      GcdFactors(b,a%b);
      var g:=Gcd(b,a%b);
      assert b==(b/g)*g;
      assert a%b==((a%b)/g)*g;
      assert a==(a/b)*b+a%b;
      var q:=(a/b)*(b/g)+(a%b)/g;
      calc { q*g; == (a/b)*((b/g)*g)+((a%b)/g)*g; == a; }
      ModExact(a,g,q,0);
    }
  }
  function FilterG(n:int,N:nat,L:seq<nat>):nat
    requires n>0 decreases |L|
  {
    if |L|==0 then N else
    var g:=FilterG(n,N,L[..|L|-1]);
    if L[|L|-1]%n==0 then Gcd(g,L[|L|-1]) else g
  }
  ghost predicate Shape(n:int,h:int,L:seq<nat>)
    requires n>1
  {
    h==1 || h==n-1 || (exists i:int :: 0<=i<|L| && ((h*L[i])%n==1 || (h*L[i])%n==n-1))
  }
  lemma Shift(e:int->int,p:int,k:int,x:int)
    requires Per(e,p)
    ensures e(x+k*p)==e(x)
    decreases if k<0 then -k else k
  {
    if k>0 {
      Shift(e,p,k-1,x);
      assert x+k*p==(x+(k-1)*p)+p;
    } else if k<0 {
      Shift(e,p,k+1,x);
      assert (x+k*p)+p==x+(k+1)*p;
    }
  }
  lemma PerGcd(e:int->int,a:nat,b:nat)
    requires Per(e,a) && Per(e,b)
    ensures Per(e,Gcd(a,b))
  {
    var u,v:=Bezout(a,b);
    forall x:int ensures e(x+Gcd(a,b))==e(x) {
      Shift(e,a,u,x); Shift(e,b,v,x+u*a);
    }
  }
  lemma DiffClass(e:int->int,n:int,h:int,N:int,x:int,l:int)
    requires Word(e,n,h,N)
    ensures Cong(e(x+l)-e(x),-h*l,n)
  {
    var a :| e(x+l)+h*(x+l)==a*n;
    var b :| e(x)+h*x==b*n;
    assert e(x+l)-e(x)+h*l==(a-b)*n;
  }
  lemma {:isolate_assertions} IntegralPer(e:int->int,n:int,h:int,N:int,l:nat)
    requires n>1 && Word(e,n,h,N) && Good(e,n,l) && l%n==0
    ensures Per(e,l)
  {
    forall x:int ensures e(x+l)==e(x) {
      DiffClass(e,n,h,N,x,l);
      var q :| e(x+l)-e(x)+h*l==q*n;
      assert l==(l/n)*n;
      var k:=q-h*(l/n);
      calc { k*n; == q*n-h*((l/n)*n); == e(x+l)-e(x); }
      if k>=1 { assert k*n>=n; } else if k<=-1 { assert k*n<=-n; }
    }
  }
  lemma FilterPer(e:int->int,n:int,h:int,N:nat,L:seq<nat>)
    requires n>1 && Word(e,n,h,N) && Pass(e,n,L)
    ensures Per(e,FilterG(n,N,L))
    decreases |L|
  {
    if |L|!=0 {
      var i:=|L|-1; var tail:=L[..i];
      assert forall j:int :: 0<=j<|tail| ==> tail[j]==L[j];
      FilterPer(e,n,h,N,tail);
      if L[i]%n==0 {
        IntegralPer(e,n,h,N,L[i]);
        PerGcd(e,FilterG(n,N,tail),L[i]);
      }
    }
  }
  lemma Step(e:int->int,n:int,h:int,N:int,s:int,x:int)
    requires n>1 && Word(e,n,h,N) && Good(e,n,s) && (h*s)%n==1
    ensures e(x+s)>=e(x)-1
  {
    DiffClass(e,n,h,N,x,s);
    var k :| e(x+s)-e(x)+h*s==k*n;
    var t:=k-(h*s)/n;
    assert e(x+s)-e(x)+1==t*n;
    if t<0 { assert t*n<=-n; }
  }
  lemma Walk(e:int->int,n:int,h:int,N:int,s:int,x:int,j:nat)
    requires n>1 && Word(e,n,h,N) && Good(e,n,s) && (h*s)%n==1
    ensures e(x+j*s)>=e(x)-j
    decreases j
  {
    if j>0 {
      Walk(e,n,h,N,s,x,j-1); Step(e,n,h,N,s,x+(j-1)*s);
      assert x+j*s==x+(j-1)*s+s;
    }
  }
  lemma Reach(e:int->int,n:int,h:int,N:int,s:int,x:int,y:int)
    requires n>1 && Word(e,n,h,N) && Per(e,n) && Good(e,n,s) && (h*s)%n==1
    ensures e(y)-e(x)>-n
  {
    var delta:=y-x; var j:=(delta*h)%n;
    var u:=(delta*h)/n; var v:=(h*s)/n;
    assert delta*h==u*n+j;
    assert h*s==v*n+1;
    calc { j*s; == (delta*h-u*n)*s; == delta*(h*s)-(u*s)*n;
           == delta+(delta*v-u*s)*n; }
    Shift(e,n,delta*v-u*s,y); Walk(e,n,h,N,s,x,j);
  }
  lemma {:isolate_assertions} Sufficient(e:int->int,n:int,h:int,N:nat,L:seq<nat>)
    requires n>1 && 0<h<n && Word(e,n,h,N) && Pass(e,n,L)
    requires FilterG(n,N,L)==n && Shape(n,h,L)
    ensures Balanced(e,n,N)
  {
    FilterPer(e,n,h,N,L);
    var t:int;
    if h==1 || h==n-1 { t:=1; ModExact(h,n,0,h); }
    else {
      var i :| 0<=i<|L| && ((h*L[i])%n==1 || (h*L[i])%n==n-1);
      t:=L[i];
    }
    var s:=t;
    if (h*t)%n!=1 {
      s:=-t;
      assert (h*t)%n==n-1;
      var k:=(h*t)/n;
      assert h*t==k*n+(n-1);
      calc { h*s; == -(h*t); == -(k*n+(n-1)); == (-k-1)*n+1; }
      ModExact(h*s,n,-(h*t/n)-1,1);
      forall x:int ensures -n<e(x+s)-e(x)<n { assert (x+s)+t==x; }
    }
    forall l:int | 1<=l<N ensures Good(e,n,l) {
      forall x:int ensures -n<e(x+l)-e(x)<n {
        Reach(e,n,h,N,s,x,x+l); Reach(e,n,h,N,s,x+l,x);
      }
    }
  }
}
