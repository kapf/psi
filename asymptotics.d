import dexpr, util;

// returns whether e1 (additively) dominates e2:
bool growsFasterThan(DVar v,DExpr e1,DExpr e2){
	e1=asymptoticNormalize(v,e1);
	e2=asymptoticNormalize(v,e2);
	return growsFasterThanNormalized(v,e1,e2);
}

bool growsFasterThanNormalized(DVar v,DExpr e1,DExpr e2){ 
	auto x1=e1,x2=one;
	if(auto p1=cast(DPow)e1){
		x1=p1.operands[0];
		x2=p1.operands[1];
	}
	auto y1=e2, y2=one;
	if(auto p2=cast(DPow)e2){
		y1=p2.operands[0];
		y2=p2.operands[1];
	}
	// dw(x1," ",x2," :: ",y1," ",y2);
	if(x1 is v && y1 is v){
		if(dIvr(DIvr.Type.leZ,x2-y2).simplify(one) is zero)
			return true;
	}
	// TODO: more cases
	return false;
}

DExpr asymptoticNormalize(DVar v,DExpr e){
	if(!e.hasFreeVar(v)) return one;
	if(auto p=cast(DPlus)e.polyNormalize(v)){
		DExprSet summands;
		foreach(s;p.summands)
			DPlus.insert(summands,asymptoticNormalize(v,s));
		DExprSet toRemove;
		foreach(s;summands)
			foreach(t;summands)
				if(s !is t && growsFasterThan(v,s,t))
					toRemove.insert(t);
		if(!toRemove.length) return p;
		foreach(x;toRemove) summands.remove(x);
		return dPlus(summands);
	}
	if(auto m=cast(DMult)e){
		DExprSet factors;
		foreach(f;m.factors)
			DMult.insert(factors,asymptoticNormalize(v,f));
		return dMult(factors);
	}
	// TODO: more cases
	return e;
}
