// Written in the D programming language.
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import dexpr, util;

import std.algorithm;
import std.typecons;

struct ℚ{
	ℤ n=0,d=1;
	this(ℤ n,ℤ d=ℤ(1)){ this.n=n;this.d=d;normalize();assert(!isNaN()); }
	this(ℤ[2] nd){ this(nd[0],nd[1]); }
	this(int n,int d=1){ this(ℤ(n),ℤ(d)); }
	this(int n,ℤ d){ this(ℤ(n),d); }
	ℚ inv(){ assert(!isZero);return ℚ(d,n); }
	ℚ abs(){ return ℚ(d.abs,n); }
	ℤ ceil(){ return -(-this).floor(); }
	ℤ floor(){
		if(d==1) return n;
		if(n>=0) return n/d;
		return -((-n+d-1)/d);
	}
	bool isNaN(){ return !n&&!d; }
	bool isZero(){ return !n&&d; }
	bool isOne(){ return n==1&&d==1; }
	bool isInfinite(){ return !d; }
	bool isPositive(){ return n>0; }
	bool isNegative(){ return n<0; }
	void normalize(){
		if(d){
			auto g=gcd(n,d);
			n/=g,d/=g;
		}else if(n){
			n=n>0?1:-1;
		}
	}
	ℚ opUnary(string op)()if(op=="-"){ return ℚ(-n,d); }
	ℚ opBinary(string op)(ℚ o)if(op=="+"||op=="-"){
		if(isInfinite||o.isInfinite){
			if(!isInfinite) return o;
			if(!o.isInfinite) return this;
			if(isPositive==o.isPositive) return this;
			assert(0);
		}
		return ℚ(mixin("n*o.d"~op~"o.n*d"),d*o.d);
	}
	ℚ opBinary(string op)(ℚ o)if(op=="*"){
		assert(!isNaN&&!o.isNaN);
		if(isInfinite&&o.isInfinite)
			return ℚ(isPositive==o.isPositive?1:-1,0);
		if(isZero||o.isZero)
			return ℚ(0,1);
		return ℚ(n*o.n,d*o.d);
	}
	ℚ opBinary(string op)(ℚ o)if(op=="/"){
		return this*o.inv;
	}
	ℚ opBinary(string op)(ℤ k)if(op=="*"){
		assert(k||!isInfinite);
		return ℚ(n*k,d);
	}
	ℚ opBinary(string op)(ℤ k)if(op=="/"){
		assert(!isZero||k!=0);
		return ℚ(n,d*k);
	}
	ℚ pow(ℤ e){
		if(e>=0) return ℚ(n.pow(e),d.pow(e));
		return ℚ(d.pow(-e),n.pow(-e));
	}
	int opCmp(ℚ o){
		if(d==0&&o.d==0) return n.opCmp(o.n);
		return (n*o.d).opCmp(o.n*d);
	}
}

struct ℚBound{
	ℚ lim;
	bool closed;
	this(ℚ lim,bool closed){
		this.lim=lim;
		this.closed=closed;
	}
	this(T)(T lim,bool closed){
		this.lim=ℚ(lim);
		this.closed=closed;
	}
	ℚBound opUnary(string op)(){
		return ℚBound(mixin(op~"lim"),closed);
	}
	ℚBound opBinary(string op)(ℚBound o){
		return ℚBound(mixin("lim"~op~"o.lim"),closed&&o.closed);
	}
	ℚBound opBinary(string op)(ℚ x){
		return ℚBound(mixin("lim"~op~"x"),closed);
	}
	ℚBound opBinary(string op)(ℤ x){
		return ℚBound(mixin("lim"~op~"x"),closed);
	}
	ℚBound opBinary(string op)(int x){
		return ℚBound(mixin("lim"~op~"x"),closed);
	}
	ℚBound abs(){ return ℚBound(lim.abs,closed); }
	ℚBound ceil(){ return -(-this).floor(); }
	ℚBound floor(){
		auto x=lim.floor;
		if(ℚ(x)==lim&&!closed) --x;
		return ℚBound(ℚ(x),true);
	}
}

struct Interval{
	ℚBound[2] lr;
	this(ℚBound l,ℚBound r){
		this.lr=[l,r];
	}
	this(S,T)(S l,bool lc,T r,bool rc){
		this.lr=[ℚBound(l,lc),ℚBound(r,rc)];
	}
	Interval opBinary(string op)(Interval o)if(op=="+"||op=="-"){
		return Interval(mixin("this[0]"~op~"o[0]"),mixin("this[1]"~op~"o[1]"));
	}
	Interval opAssign(string op)(Interval o)if(op=="+"||op=="-"){
		this=mixin("this"~op~"o");
	}
	bool empty() { return lr[0].lim==lr[1].lim&&(!lr[0].closed||!lr[1].closed); }
	ℚBound opIndex(int i){ return lr[i]; }
};
Interval iPoint(T)(T x){ return iClosed(x,x); }
Interval iClosed(S,T)(S l,T r){ return Interval(l,true,r,true); }
Interval iOpen(S,T)(S l,T r){ return Interval(l,false,r,false); }
Interval iLeftOpen(S,T)(S l,T r){ return Interval(l,false,r,true); }
Interval iRightOpen(S,T)(S l,T r){ return Interval(l,true,r,false); }
Interval iLeftBounded(T)(T l,bool closed=true){ return Interval(l,closed,ℚ(1,0),false); }
Interval iRightBounded(T)(T r,bool closed=true){ return Interval(ℚ(-1,0),false,r,closed); }
Interval iAll(){ return Interval(ℚ(-1,0),false,ℚ(1,0),false); }
Interval iEmpty(){ return Interval(ℚ(0,1),false,ℚ(0,1),false); }
Interval iCombine(Interval a,Interval b){
	if(a.empty) return b;
	if(b.empty) return a;
	return Interval(minB(a[0],b[0]),maxB(a[1],b[1]));
}
Interval iIntersect(Interval a,Interval b){
	auto l=maxB(a[0],b[0]);
	auto r=minB(a[1],b[1]);
	if(r.lim>l.lim) return iEmpty();
	return Interval(l,r);
}

ℚBound exclB(S,T)(S n,T d=1){ return ℚBound(ℚ(n,d),false); }
ℚBound inclB(S,T)(S n,T d=1){ return ℚBound(ℚ(n,d),true); }

ℚBound maxB(ℚBound a,ℚBound b){
	if(a.lim==b.lim) return a.closed?a:b;
	return a.lim>b.lim?a:b;
}
ℚBound minB(ℚBound a,ℚBound b){
	if(a.lim==b.lim) return a.closed?a:b;
	return a.lim<b.lim?a:b;
}
bool containsZero(Interval b){
	return (b[0].lim.isNegative||(b[0].lim.isZero&&b[0].closed))&&(b[1].lim.isPositive||(b[1].lim.isZero&&b[0].closed));
}
bool nearZero(Interval b){
	return !b[0].lim.isPositive&&!b[1].lim.isNegative;
}

Interval bPowℤ(Interval b,ℤ e){
	if(e==1) return b;
	if(e==0) return iClosed(b.containsZero?0:1,1);
	if(e>=2){
		if(e%2==0){
			if(b.nearZero){
				auto r=maxB(b[0].abs,b[1].abs);
				r.lim=r.lim.pow(ℤ(e));
				return Interval(ℚBound(0,b.containsZero),r);
			}
			if (b[0].lim.isNegative){
				//swap(b[0],b[1]);
				auto tmp=b[0];
				b[0]=b[1];
				b[1]=tmp;
			}
		}
		b[0].lim=b[0].lim.pow(ℤ(e));
		b[1].lim=b[1].lim.pow(ℤ(e));
		return b;
	}
	assert(e<0);
	if(b.nearZero){
		if(b[0].lim.isNegative&&b[1].lim.isPositive) return iAll();
		if(b[0].lim.isNegative) return iRightBounded(0,false);
		if(b[1].lim.isPositive) return iLeftBounded(0,false);
		return iEmpty();
	}
	auto l=ℚBound(b[0].lim.inv,b[0].closed),r=ℚBound(b[1].lim.inv,b[1].closed);
	if(l.lim>r.lim) swap(l,r);
	return bPowℤ(Interval(l,r),-e);
}

Interval bRoot(ℚ a,ℤ n,int k) {
	// calculate [floor((a*16^(k*n))^-n)/16^k,ceil((a*16^(k*n))^-n)/16^k]
	// this isn't the fastest converging method, but the representation in ℚ doesn't explode
	// TODO: return exact result if a rational root exists
	if(a.isNegative) return iEmpty();
	ℤ denum=ℤ(16).pow(ℤ(k));
	a=a*denum.pow(n);
	ℤ l=0,r=a.ceil();
	while (r-l>1){
		auto m=(l+r)/2;
		if(m.pow(n)*a.d<=a.n)
			l=m;
		else
			r=m;
	}
	assert(l<r);
	assert(l.pow(n)*a.d<=a.n);
	assert(r.pow(n)*a.d>a.n);
	return iRightOpen(ℚ(l,denum),ℚ(r,denum));
}

Interval bPowℚ(Interval b,ℚ e,int k) {
	auto bb=b.bPowℤ(e.n);
	return iCombine(bb[0].lim.bRoot(e.d,k),bb[1].lim.bRoot(e.d,k));
}
Interval bPowInterval(Interval b,Interval e,int k) {
	Interval doℚ(Interval b,Interval e,int k) {
		b=iIntersect(e,iLeftBounded(0));
		auto x1=b.bPowℚ(e[0].lim,k);
		auto x2=b.bPowℚ(e[1].lim,k);
		return iCombine(x1,x2); // TODO: not using that e doesn't need to be closed
	}
	Interval doℤ(Interval b,Interval e) {
		auto e0=e[0].ceil(),e1=e[1].floor();
		assert(e0.closed&&e1.closed&&e0.lim.d==1&&e1.lim.d==1);
		if(e0.lim.d>e1.lim.d) return iEmpty();
		return iCombine(b.bPowℤ(e0.lim.n),b.bPowℤ(e1.lim.n));
	}
	return iCombine(doℚ(b,e,k),doℤ(b,e));
}

Interval approxE(int k){
	ℤ n=2,d=1;
	for(int i=2;i<=10*k;i++)n*=i,n+=1,d*=i;
	return iOpen(ℚ(n,d),ℚ(n+1,d));
}
Interval approxΠ(int k){
	if(k==0) return iOpen(3,4);
	auto lim=ℚBound(0,false);
	ℤ p16=1;
	for(int n=0;n<=k;++n,p16*=16){
		lim=lim+exclB(1,p16)*(exclB(4,8*n+1)-exclB(2,8*n+4)-exclB(1,8*n+5)-exclB(1,8*n+6));
	}
	return Interval(lim,lim+exclB(4,p16));
}

Interval getBound(DExpr e,int k){
	if(e.isFraction)return iPoint(ℚ(e.getFraction));
	if(cast(DE)e) return approxE(k);
	if(cast(DΠ)e) return approxΠ(k);
	if(auto s=cast(DPlus)e){
		auto lim=iPoint(0);
		foreach(s;s.summands)
			lim=lim+s.getBound(k);
		return lim;
	}
	if(auto p=cast(DPow)e){
		if(auto ex=cast(Dℤ)p.operands[1])
			return p.operands[0].getBound(k).bPowℤ(ex.c);
		if(p.operands[1].isFraction)
			return p.operands[0].getBound(k).bPowℚ(ℚ(p.operands[1].getFraction),k);
		return p.operands[0].getBound(k).bPowInterval(p.operands[1].getBound(k),k);
	}
	if(auto m=cast(DMult)e){
		auto l=inclB(1),u=inclB(1);
		foreach(f;m.factors){
			auto bb=getBound(f,k);
			auto l1=l*bb[0],u1=u*bb[0];
			if(bb[0].lim.isNegative) swap(l1,u1);
			auto l2=l*bb[1],u2=u*bb[1];
			if(bb[1].lim.isNegative) swap(l2,u2);
			l=minB(l1,l2);
			u=maxB(u1,u2);
		}
		return Interval(l,u);
	}
	if(auto g=cast(DGaussInt)e){
		if (k==0) return iLeftBounded(0,false);
		if (k<=1) return iOpen(0,3);
		return iOpen(ℤ(0),bRoot(approxΠ(k)[1].lim,ℤ(2),k)[1].lim);
	}
	if(cast(DIvr)e) return iClosed(0,1);
	return iAll(); // not implemented
}

immutable maxIterations=10;

Nullable!bool boundcheckLeZ(DExpr e){
	for(int k=0;k<=maxIterations;++k){
		auto b=getBound(e,k);
		if(b[1].lim.isNegative||(b[1].lim.isZero)) return Nullable!bool(true);
		if(b[0].lim.isPositive||(b[0].lim.isZero&&!b[0].closed)) return Nullable!bool(false);
	}
	return Nullable!bool();
}
Nullable!bool boundcheckEqZ(DExpr e){
	for(int k=0;k<=maxIterations;++k){
		auto b=getBound(e,k);
		if(!b.containsZero)return Nullable!bool(false);
		if(b.empty) return Nullable!bool(false);
		if(b[0].lim.isZero&&b[0].lim.isZero) return Nullable!bool(true);
	}
	return Nullable!bool();
}
Nullable!bool negateNullableBool(Nullable!bool b){
	if(!b.isNull) return Nullable!bool(!b.get);
	return b;
}
Nullable!bool boundcheckNeqZ(DExpr e){
	return negateNullableBool(boundcheckEqZ(e));
}
Nullable!bool boundcheckLZ(DExpr e){
	return negateNullableBool(boundcheckLeZ(-e));
}
