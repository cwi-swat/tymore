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

import Type;

@doc{Type monad with identity behaviour}
public data TypeOf[&T] = typeof(&T v) | tzero();
public TypeOf[&T] returnT(&T v) = typeof(v);
public TypeOf[&T2] bind(typeof(&T1 v), TypeOf[&T2] (&T1) f) = f(v);
public TypeOf[&T2] bind(tzero(), TypeOf[&T2] (&T1) f) = tzero();

public bool isZero(tzero()) = true;
public default bool isZero(TypeOf[&T] mv) = false;

@doc{SubstsT monad that adds explicit substitution aspect to values (type value in this case)}
public data SubstsT[&T] = substs( TypeOf[tuple[&T,Substs]] (Substs) v );

public SubstsT[&T] returnS(&T v) = substs(TypeOf[tuple[&T,Substs]] (Substs s) { return returnT(<v, s>); });
public TypeOf[tuple[&T,Substs]] (Substs) run(SubstsT[&T] mv) = mv.v;
public SubstsT[&T] runWithEmptySubsts(SubstsT[&T] mv) {
	TypeOf[tuple[&T,Substs]] v = run(mv)(substs([],[]));
	return substs( TypeOf[tuple[&T,Substs]] (Substs _) { return v; } );
}
public TypeOf[&T] eval(SubstsT[&T] mv) = bind(mv.v(substs([],[])), TypeOf[&T] (tuple[&T, Substs] v) { return returnT(v[0]); });

public SubstsT[&T2] bind(SubstsT[&T1] mv, SubstsT[&T2] (&T1) f)
	= substs( TypeOf[tuple[&T2,Substs]] (Substs s) {
				TypeOf[tuple[&T1,Substs]] v = run(mv)(s);
				return bind(v, TypeOf[tuple[&T2,Substs]] (tuple[&T1,Substs] tpl) { 
							return run(f(tpl[0]))(tpl[1]); });
			  } );
			  
public bool isZero(SubstsT[&T] mv) = isZero(eval(mv));

@doc{Drops the substitution part}
public SubstsT[&T] discard(SubstsT[&T] mv)
	= substs( TypeOf[tuple[&T,Substs]] (Substs s) {
				TypeOf[tuple[&T,Substs]] v = run(mv)(s);
				return bind(v, TypeOf[tuple[&T,Substs]] (tuple[&T,Substs] v_) { 
							return returnT(<v_[0], substs([],[])>); }); });
			  
public SubstsT[&T] catchZ(SubstsT[&T] mv1, SubstsT[&T] mv2) 
	= substs( TypeOf[tuple[&T,Substs]] (Substs s) {
				TypeOf[tuple[&T,Substs]] v1 = run(mv1)(s);
				if(!(tzero() := v1)) return v1;
				TypeOf[tuple[&T,Substs]] v2 = run(mv2)(s);
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

@doc{SubstsT' monad that adds explicit substitution to non-deterministic value computation}
public data SubstsT_[&T] = substs_( lrel[&T,Substs] (Substs) v );

public SubstsT_[&T] returnS_(&T v) = substs_(lrel[&T,Substs] (Substs s) { return [<v, s>]; });
public lrel[&T,Substs] (Substs) run(SubstsT_[&T] mv) = lrel[&T,Substs] (Substs s) { return mv.v(s); };
public SubstsT_[&T] runWithEmptySubsts(SubstsT_[&T] mv) = substs_( lrel[&T,Substs] (Substs _) { return run(mv)(substs([],[])); } );
public list[&T] eval(SubstsT_[&T] mv) = [ v[0] | tuple[&T,Substs] v <- mv.v(substs([],[])) ];

public SubstsT_[&T2] bind(SubstsT_[&T1] mv, SubstsT_[&T2] (&T1) f)
	= substs_( lrel[&T2,Substs] (Substs s) {
					lrel[&T1,Substs] vs = run(mv)(s);
					return [ *run(f(v[0]))(v[1]) | tuple[&T1, Substs] v <- vs ];
			  } );
			  
public SubstsT_[&T] discard(SubstsT_[&T] mv)
	= substs_( lrel[&T,Substs] (Substs s) {
				lrel[&T,Substs] vs = run(mv)(s);
				return [ <v,substs([],[])> | <&T v, Substs _> <- vs ]; });

			  
public SubstsT_[&T] concat(SubstsT_[&T] mv1, SubstsT_[&T] mv2)
	= substs_(lrel[&T, Substs] (Substs substs) {
		return run(mv1)(substs) + run(mv2)(substs); });
			  
public SubstsT_[&T] lift(list[&T] vs) = !isEmpty(vs) ? substs_( lrel[&T, Substs] (Substs s) { return [ <v, s> | &T v <- vs ]; })
													 : substs_( lrel[&T, Substs] (Substs s) { return []; });

public bool isZero(SubstsT_[&T] mv) = isEmpty(eval(mv));
													 
@doc{SubstsTL monad that adds explicit substitution in a slightly different manner}
public data SubstsTL[&T] = substsl(TypeOf[tuple[&T,list[Substs]]] val);

public SubstsTL[&T] returnSL(&T v) = substsl(returnT(<v, []>));
public TypeOf[tuple[&T,list[Substs]]] run(SubstsTL[&T] mv) = mv.val;
public TypeOf[&T] eval(SubstsTL[&T] mv) 
	= bind(mv.val, TypeOf[&T] (tuple[&T,list[Substs]] v) { 
			return returnT(v[0]); });

public SubstsTL[&T2] bind(SubstsTL[&T1] _:substsl( TypeOf[tuple[&T1,list[Substs]]] mv1 ), SubstsTL[&T2] (&T1) f)
	= substsl( bind(mv1, TypeOf[tuple[&T2,list[Substs]]] (tuple[&T1,list[Substs]] v1) { 
						SubstsTL[&T2] mv2 = f(v1[0]);
						return bind(mv2.val, TypeOf[tuple[&T2,list[Substs]]] (tuple[&T2,list[Substs]] v2) {
									return returnT(<v2[0], v1[1] + v2[1]>); } ); }) );

public bool isZero(SubstsTL[&T] mv) = isZero(eval(mv));

public SubstsTL[&T] liftTL(TypeOf[&T] mv) 
	= substsl( bind(mv, TypeOf[tuple[&T,list[Substs]]] (&T v) { 
					return returnT(<v, []>); }) );

@doc{SubstsTL' monad}
public data SubstsTL_[&T] = substsl_( rel[&T,list[Substs]] v); // promising experience of replacing list to set logic of computation

public SubstsTL_[&T] returnSL_(&T v) = substsl_({<v, []>});
public rel[&T,list[Substs]] run(SubstsTL_ mv) = mv.v;
public set[&T] eval(SubstsTL_[&T] mv) = { v | <&T v, _> <- mv.v };
public set[list[Substs]] evalSubsts(SubstsTL_[&T] mv) = { ss | <&T _, list[Substs] ss> <- mv.v };

public SubstsTL_[&T2] bind(SubstsTL_[&T1] _:substsl_( rel[&T1,list[Substs]] vs1 ), SubstsTL_[&T2] (&T1) f)
	= substsl_({ <v2, substs1 + substs2> | <&T1 v1, list[Substs] substs1> <- vs1, 
										   <&T2 v2, list[Substs] substs2> <- run(f(v1)) });
	
public SubstsTL_[&T] liftTL_(set[&T] vs) = !isEmpty(vs) ? substsl_( { <v, []> | &T v <- vs } )
													    : substsl_( {} );
													    
public bool isZero(SubstsTL_[&T] mv) = isEmpty(eval(mv));

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
	return substsl(bind(v, TypeOf[tuple[&T,list[Substs]]] (tuple[&T,Substs] v_) { return returnT(<v_[0], (v_[1] != substs([],[])) ? [ v_[1] ] : []>); }));
} 

@doc{tauToSubstsT: SubstsTL -> SubstsT}
public SubstsT[&T] tauToSubstsT(SubstsTL[&T] mv) {
	TypeOf[tuple[&T,list[Substs]]] v = run(mv);
	return substs( TypeOf[tuple[&T,Substs]] (Substs s) {
						return bind(v, TypeOf[tuple[&T,Substs]] (tuple[&T,list[Substs]] v_) { return returnT(<v_[0], (!isEmpty(v_[1])) ? v_[1][0] : substs([],[]) >); }); });
}

// TODO: rename to tau
@doc{tauToSubstsT: SubstsTL -> SubstsTL'}
public SubstsTL_[&T] tauToSubstsTL_(SubstsTL[&T] mv) {
	TypeOf[tuple[&T,list[Substs]]] v = run(mv);
	return substsl_( typeof(tuple[&T,list[Substs]] v_) := v ? { v_ } : {} );
}

@doc{tauToSubstsTL_: SubstsT -> SubstsTL'}
public SubstsTL_[&T] tauToSubstsTL_(SubstsT[&T] mv) {
	return tauToSubstsTL_(tau(mv));
}

@doc{tauToSubstsTL_: SubstsT' -> SubstsTL'}
public SubstsTL_[&T] tauToSubstsTL_(SubstsT_[&T] mv) {
	lrel[&T,Substs] vs = run(mv)(substs([],[]));
	return substsl_({ <v, (substs != Substs::substs([],[])) ? [ substs ] : [] > | <&T v, Substs substs> <- vs });
} 

@doc{tauToSubstsT_: SubstsTL' -> SubstsT'}
public SubstsT_[&T] tauToSubstsT_(SubstsTL_[&T] mv) {
	rel[&T,list[Substs]] vs = run(mv);
	return substs_( lrel[&T,Substs] (Substs s) {
						return [ <v, (!isEmpty(ss)) ? ss[0] : substs([],[]) > | <&T v, list[Substs] ss> <- vs ]; });
} 
		
@doc{tau: TypeOf -> list}
public list[&T] tau(TypeOf[&T] mv) 
	= typeof(&T v) := mv ? [ v ] : [];
public TypeOf[&T] tauInv(list[&T] mv) 
	= isEmpty(mv) ? tzero() : returnT(head(mv));
	

@doc{Prettyprinting facilities}		
public str prettyprint(typeof(&T v)) = prettyprint(v);
public str prettyprint(tzero()) = "zero";

public str prettyprint(SubstsT[&T] mv) {
	//TypeOf[tuple[Entity,Substs]] v = run(mv)(substs([],[]));
	TypeOf[Entity] v = eval(mv);
	return prettyprint(v);
}

public str prettyprint(SubstsTL[&T] mv) {
	//TypeOf[tuple[Entity,list[Substs]]] v = run(mv);
	TypeOf[Entity] v = eval(mv);
	return prettyprint(v);
}

public str prettyprint(substsl_(rel[&T, list[Substs]] vals)) = "[ <for(val<-vals){><prettyprint(val)><}> ]";
public str prettyprint(<&T v, Substs ss>) = "\< <prettyprint(v)>, <prettyprint(ss)> \>";
public str prettyprint(<&T v, list[Substs] ss>) = "\< <prettyprint(v)>, <for(substs<-ss){><prettyprint(substs)><}> \>";
