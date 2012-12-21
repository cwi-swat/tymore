@doc{The module defines the monadic infrastructure of the framework in terms of specific 'monads' and 'monad transformers'; 
	 remark: it provides a nice way of playing with incremental semantics of computations, however, one has to be careful}
module typecomputations::TypeMonadTransformers

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;
import lang::java::jdt::refactorings::PrettyPrintUtil;

import typecomputations::SemanticDomains;
import typecomputations::TypeValues;
import typecomputations::TypeValuesPlusGens;

import Prelude;


@doc{Fixed base monad}
data TypeOf[&F] = typeof(&F val)
			  	| typeid(&F val) // to make explicit the existence of simple types vs. constraint variables
			  	;			  	  	
public TypeOf[&F] inclTypeOf(&F val) = typeof(val);
public TypeOf[&F1] bind(TypeOf[&F] val, TypeOf[&F1] (&F) f) { 
	switch (val) { 
		case typeof(&F v): return f(v);
		case typeid(&F v): return typeid(v);
	};
}
public Option[&F] run(typeof(&F val)) = some(val);
public default Option[&F] run(TypeOf[&F] val) = none();

public TypeOf[&F] fetchv(typeid(&F val)) = inclTypeOf(val); 
public default TypeOf[&F] fetchv(TypeOf[&F] val) = val;

public TypeOf[&F] toConst(&F val) = typeid(val);

@doc{Monad that models computations with multiple results}
data SetTypeOf[&F] = settypeof(set[TypeOf[&F]] vals)
				   ;
public SetTypeOf[&F] inclSet(&F val) = settypeof({ inclTypeOf(val) });
public SetTypeOf[&F1] bind(SetTypeOf[&F] mvals, SetTypeOf[&F1] (&F) f) 
	= settypeof({ *( (some(&F v) := run(mval)) ? run(f(v)) : { mval } ) | TypeOf[&F] mval <- mvals.vals })
	;
public set[TypeOf[&F]] run(settypeof(set[TypeOf[&F]] vals)) = vals;
public SetTypeOf[&F] liftSet(TypeOf[&F] mval) = settypeof({ mval });	

@doc{Monad modelling stateful computations}
data StateTypeOf[&F] = statetypeof(SetTypeOf[tuple[&F, AstNode]] (AstNode) val)
					 ;
public StateTypeOf[&F] inclState(&F val) 
	= statetypeof(SetTypeOf[tuple[&F, AstNode]] (AstNode t) { return inclSet(<val, t>); })
	;
public StateTypeOf[&F1] bind(StateTypeOf[&F] mval, StateTypeOf[&F1] (&F) f)
	= statetypeof( SetTypeOf[tuple[&F1, AstNode]] (AstNode t) { 
		return settypeof( { *( (some(<&F v, AstNode tt>) := run(val)) ? run(run(tt, f(v))) : { val } ) 
								| TypeOf[tuple[&F, AstNode]] val <- run(mval.val(t)) } ); } )
	;
public StateTypeOf[&F3] bind(StateTypeOf[&F1] mval1, StateTypeOf[&F2] mval2, StateTypeOf[&F3] (&F1, &F2) f) 
	/*
	= statetypeof( SetTypeOf[tuple[&StF33, AstNode]] (AstNode t) { 
		return { *( (typeof(<&StF31 v1, AstNode tt>) := val1) ? { *( (typeof(<&StF32 v2, AstNode ttt>) := val2) ? run(run(ttt, f(v1, v2))) : { val2 } ) 
																| TypeOf[&StF32, AstNode] val2 <- run(tt, mval2) } : { val1 } ) 
						| TypeOf[&StF31, AstNode] val1 <- run(t, mval1) }; } )
	*/
	= bind(mval1, StateTypeOf[&F3] (&F1 val1) { return bind(mval2, StateTypeOf[&F3] (&F2 val2) { return f(val1, val2); }); })
	;		
public SetTypeOf[tuple[&F, AstNode]] run(AstNode t, StateTypeOf[&F] mval) 
	= mval.val(t)
	;
public StateTypeOf[AstNode] fetchSTerm() 
	= statetypeof(SetTypeOf[tuple[AstNode, AstNode]] (AstNode t) { return inclSet(<t, t>); })
	;		
public StateTypeOf[AstNode] assignSTerm(AstNode t) 
	= statetypeof(SetTypeOf[tuple[AstNode, AstNode]] (AstNode tt) { return inclSet(<t, t>); })
	;
@doc{Extra state}
data M[&F] = statetypeof2(StateTypeOf[&F] (CompilUnit, Mapper) val)
		   ;
public M[&F] inclM(&F val) 
	= statetypeof2(StateTypeOf[&F] (CompilUnit facts, Mapper mapper) { return inclState(val); })
	;
public M[&F1] bind(M[&F] mval, M[&F1] (&F) f)
	= statetypeof2( StateTypeOf[&F1] (CompilUnit facts, Mapper mapper) {
		return statetypeof( SetTypeOf[tuple[&F1, AstNode]] (AstNode t) {
			return settypeof( { *( (some(<&F v, AstNode tt>) := run(val)) ? run(run(tt, run(facts, mapper, f(v)))) : { val } )
									| TypeOf[tuple[&F, AstNode]] val <- run(run(t, mval.val(facts, mapper))) } ); } ); })
	;
public M[&F3] bind(M[&F1] mval1, M[&F2] mval2, M[&F3] (&F1, &F2) f) 
	= bind(mval1, M[&F3] (&F1 val1) { return bind(mval2, M[&F3] (&F2 val2) { return f(val1, val2); }); })
	;		
public StateTypeOf[&F] run(CompilUnit facts, Mapper mapper, M[&F] mval) 
	= mval.val(facts, mapper)
	;
public M[CompilUnit] fetchMFacts() 
	= statetypeof2(StateTypeOf[CompilUnit] (CompilUnit facts, Mapper _) { return inclState(facts); })
	;
public M[Mapper] fetchMMapper() 
	= statetypeof2(StateTypeOf[Mapper] (CompilUnit _, Mapper mapper) { return inclState(mapper); })
	;
@doc{Lifting functions}
public StateTypeOf[&F] liftState(TypeOf[&F] mval) 
	 = statetypeof(SetTypeOf[tuple[&F, AstNode]] (AstNode t) { 
	 	return liftSet( ( (some(&F val) := run(mval)) ? inclTypeOf(<val, t>) 
													: bind(bind(fetchv(mval), 
																TypeOf[tuple[&F, AstNode]] (&F v) { 
																	return inclTypeOf(<v, t>); }), 
														   TypeOf[tuple[&F, AstNode]] (tuple[&F, AstNode] v) { return toConst(v); }) )); 
	  })
	;
public StateTypeOf[&F] liftState(SetTypeOf[&F] mval) 
	= statetypeof(SetTypeOf[tuple[&F, AstNode]] (AstNode t) { 
		return bind(mval, SetTypeOf[tuple[&F, AstNode]] (&F v) { return inclSet(<v, t>); } ); })
	;
public StateTypeOf[&F] liftState(StateTypeOf[&F] mval) = mval;

public M[&F] liftM(TypeOf[&F] mval) 
	= statetypeof2(StateTypeOf[&F] (CompilUnit facts, Mapper mapper) {
		return liftState(mval); } )
	;
public M[&F] liftM(SetTypeOf[&F] mval) 
	= statetypeof2(StateTypeOf[&F] (CompilUnit facts, Mapper mapper) { 
		return liftState(mval); })
	;
public M[&F] liftM(StateTypeOf[&F] mval) 
	= statetypeof2(StateTypeOf[&F] (CompilUnit facts, Mapper mapper) { return mval; })
	;
public M[&F] liftM(M[&F] mval) = mval;
public M[&F] (M[&F]) liftM(TypeOf[&F] (TypeOf[&F]) f) 
	= M[&F] (M[&F] mval) { 
		return statetypeof2( StateTypeOf[&F] (CompilUnit facts, Mapper mapper) {
			return statetypeof(SetTypeOf[tuple[&F, AstNode]] (AstNode t) {
				return settypeof({ f(val) | TypeOf[tuple[&F, AstNode]] val <-  run(run(t, mval.val(facts, mapper))) }); }); } ); }
	;
public default M[&F] liftM(&F val) = inclM(val);

@doc{Execute computations}
public set[TypeOf[tuple[&F, AstNode]]] execute(CompilUnit facts, Mapper mapper, AstNode t, M[&F] val) = run(run(t, run(facts, mapper, val)));

@doc{Ordinary composition}
public &F1 comp(&F val, &F1 (&F) f) = f(val); 
