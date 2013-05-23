@license{
  Copyright (c) 2009-2011 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - A.Izmaylova@cwi.nl}
module prototype::computations::mksubsts::Monads

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import prototype::lang::java::jdt::refactorings::Java;
import prototype::lang::java::jdt::refactorings::JavaADT;
import prototype::lang::java::jdt::refactorings::PrettyPrintUtil;
import prototype::lang::java::jdt::refactorings::ValuesUtil;

import prototype::computations::mksubsts::LanguageInterface;
import prototype::computations::mksubsts::FunctionsOfTypeValues;

import IO;
import List;
import Map;
import Set;

// Type monad
public data TypeOf[&T] = typeof(&T v) | tzero();
public TypeOf[&T] returnT(&T v) = typeof(v);
public TypeOf[&T2] bind(typeof(&T1 v), TypeOf[&T2] (&T1) f) = f(v);
public TypeOf[&T2] bind(tzero(), TypeOf[&T2] (&T1) f) = tzero();

public bool isZero(tzero()) = true;
public default bool isZero(TypeOf[&T] mv) = false;

// SubstsT monad
public data SubstsT[&T] = substs( TypeOf[tuple[&T, Substs]] (Substs) v );

public SubstsT[&T] returnS(&T v) = substs(TypeOf[tuple[&T, Substs]] (Substs s) { return returnT(<v, s>); });
public TypeOf[tuple[&T, Substs]] (Substs) run(SubstsT[&T] mv) = TypeOf[tuple[&T, Substs]] (Substs s) { return mv.v(s); };
public TypeOf[&T] eval(SubstsT[&T] mv) = bind(mv.v(substs([],[])), TypeOf[&T] (tuple[&T, Substs] v) { return returnT(v[0]); });

@doc{Drops the substitution part}
public SubstsT[&T] discard(SubstsT[&T] mv)
	= substs( TypeOf[tuple[&T, Substs]] (Substs s) {
				TypeOf[tuple[&T, Substs]] v = run(mv)(substs([],[]));
				return (typeof(<&T v_,_>) := v) ? returnT(<v_,s>) : tzero() ; } );

public SubstsT[&T2] bind(SubstsT[&T1] mv, SubstsT[&T2] (&T1) f)
	= substs( TypeOf[tuple[&T2, Substs]] (Substs s) {
				TypeOf[tuple[&T1, Substs]] v = run(mv)(s);
				return (typeof(tuple[&T1, Substs] tpl) := v) ? run(f(tpl[0]))(tpl[1]) : tzero();
			  } );
			  
public bool isZero(SubstsT[&T] mv) = isZero(eval(mv));
			  
public SubstsT[&T] catchZ(SubstsT[&T] mv1, SubstsT[&T] mv2) 
	= substs( TypeOf[tuple[&T, Substs]] (Substs s) {
				TypeOf[tuple[&T, Substs]] v1 = run(mv1)(s);
				if(!(tzero() := v1)) return v1;
				TypeOf[tuple[&T, Substs]] v2 = run(mv2)(s);
				return v2 ; } );
			  
public SubstsT[&T] lift(TypeOf[&T] v) 
	= (typeof(&T v_) := v) ? substs(TypeOf[tuple[&T, Substs]] (Substs s) { return returnT(<v_, s>); }) 
						   : substs(TypeOf[tuple[&T, Substs]] (Substs _) { return tzero(); });

			  
public SubstsT[value] appnd(Substs s) = substs(TypeOf[tuple[value, Substs]] (Substs ps) { return returnT(<zero(), concat(ps, s)>); });
public SubstsT[Substs] popSubsts() = substs(TypeOf[tuple[Substs, Substs]] (Substs s) { return returnT(<s, s>); });

public SubstsT[Entity] (Mapper, Entity) pushSubsts(Substs (Substs) f) 
	= SubstsT[Entity] (Mapper mapper, Entity v) {
		Substs s = getSubsts(mapper, v);
		return bind(appnd(f(s)), SubstsT[Entity] (value _) { return returnS(v); });
	};

// SubstsT' monad
public data SubstsT_[&T] = substs_( lrel[&T, Substs] (Substs) v );

public SubstsT_[&T] returnS_(&T v) = substs_(lrel[&T, Substs] (Substs s) { return [<v, s>]; });
public lrel[&T, Substs] (Substs) run(SubstsT_[&T] mv) = lrel[&T, Substs] (Substs s) { return mv.v(s); };
public list[&T] eval(SubstsT[&T] mv) = [ v[0] | tuple[&T, Substs] v <- mv.v(substs([],[])) ];

public SubstsT_[&T2] bind(SubstsT_[&T1] mv, SubstsT_[&T2] (&T1) f)
	= substs_( lrel[&T2, Substs] (Substs s) {
					lrel[&T1, Substs] vs = run(mv)(s);
					return [ *run(f(v[0]))(v[1]) | tuple[&T1, Substs] v <- vs ];
			  } );
			  
public SubstsT_[&T] lift(list[&T] vs) = !isEmpty(vs) ? substs_( lrel[&T, Substs] (Substs s) { return [ <v, s> | &T v <- vs ]; })
													 : substs_( lrel[&T, Substs] (Substs s) { return []; });
													 
// SubstsTL monad
public data SubstsTL[&T] = substsl( TypeOf[tuple[&T,Substs]] v);

public SubstsTL[&T] returnSL(&T v) = substsl(returnT(<v,substs([],[])>));
public TypeOf[tuple[&T,Substs]] run(SubstsTL[&T] mv) = mv.v;

public SubstsTL[&T2] bind(SubstsTL[&T1] _:substsl( TypeOf[tuple[&T1,Substs]] mv1 ), SubstsTL[&T2] (&T1) f) {
	switch(mv1) {
		case typeof(<&T1 v, Substs substs>): return f(v);
		default: return substsl(tzero());
	}
}

// SubstsTL' monad
public data SubstsTL_[&T] = substsl_( lrel[&T,Substs] v);

public SubstsTL_[&T] returnSL_(&T v) = substsl_([<v,substs([],[])>]);
public lrel[&T,Substs] run(SubstsTL_ mv) = mv.v;
public list[&T] eval(SubstsTL_[&T] mv) = [ v | <&T v, _> <- mv.v ];

public SubstsTL_[&T2] bind(SubstsTL_[&T1] _:substsl_( lrel[&T1,Substs] mv1 ), SubstsTL_[&T2] (&T1) f)
	= substsl_([ *run(f(v)) | <&T1 v, _> <- mv ]);

@doc{tau: SubstsT -> SubstsT'}
public SubstsT_[&T] tau(SubstsT[&T] mv) 
	= substs_( list[tuple[&T, Substs]] (Substs s) {
		TypeOf[tuple[&T, Substs]] v = run(mv)(s);
		return tau(v); });
public SubstsT[&T] tauInv(SubstsT_[&T] mv) 
	= substs( TypeOf[tuple[&T, Substs]] (Substs s) {
		list[tuple[&T, Substs]] v = run(mv)(s);
		return tauInv(v); });
		
@doc{tauToSubstsTL: SubstsT -> SubstsTL}
public SubstsTL[&T] tauToSubstsTL(SubstsT[&T] mv) {
	TypeOf[tuple[&T,Substs]] v = run(mv)(substs([],[]));
	return substsl(v);
} 

@doc{tauToSubstsT: SubstsTL -> SubstsT}
public SubstsT[&T] tauToSubstsT(SubstsTL[&T] mv) {
	TypeOf[tuple[&T,Substs]] v = run(mv);
	return substs( TypeOf[tuple[&T,Substs]] (Substs s) {
						return v; });
}

@doc{tauToSubstsTL_: SubstsT_ -> SubstsTL_}
public SubstsTL_[&T] tauToSubstsTL_(SubstsT_[&T] mv) {
	lrel[&T,Substs] v = run(mv)(substs([],[]));
	return substsl_(v);
} 

@doc{tauToSubstsT_: SubstsTL_ -> SubstsT_}
public SubstsT_[&T] tauToSubstsT_(SubstsTL_[&T] mv) {
	lrel[&T,Substs] v = run(mv);
	return substs_( lrel[&T,Substs] (Substs s) {
						return v; });
} 
		
@doc{tau: TypeOf -> list}
public list[&T] tau(TypeOf[&T] mv) 
	= typeof(&T v) := mv ? [ v ] : [];
public TypeOf[&T] tauInv(list[&T] mv) 
	= isEmpty(mv) ? tzero() : returnT(head(mv));
		
public str prettyprint(typeof(&T v)) = prettyprint(v);
public str prettyprint(tzero()) = "zero";
