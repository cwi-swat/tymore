@doc{The module defines the monadic infrastructure of the framework in terms of specific 'monads' and 'monad transformers'; 
	 remark: it provides a nice way of playing with incremental semantics of computations, however, one has to be careful}
module typecomputations::ConstraintMonadTransformers

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;
import lang::java::jdt::refactorings::PrettyPrintUtil;

import typecomputations::SemanticDomains;
import typecomputations::TypeValues;
import typecomputations::TypeValuesPlusGens;
import typecomputations::TypeMonadTransformers;

import Prelude;


data Constraint[&Mon] = eq(&Mon lh, &Mon rh)
					  | subtype(&Mon lh, &Mon rh);

@doc{Fixed base monad}
data MId[&F] = mid(&F val)
  		  	 ;			  	  	
public MId[&F] inclMId(&F val) = mid(val);
public MId[&F1] bind(MId[&F] mval, MId[&F1] (&F) f)
	= mval.val;
public Option[&F] run(mid(&F val)) = some(val);
 
@doc{Monad that models computations with multiple results}
data SetMId[&F] = setmid(set[MId[&F]] vals)
				   ;
public SetMId[&F] inclSetMId(&F val) = setmid({ inclMId(val) });
public SetMId[&F1] bind(SetMId[&F] mvals, SetMId[&F1] (&F) f) 
	= setmid({ *( (some(&F v) := run(mval)) ? run(f(v)) : { mval } ) | MId[&F] mval <- mvals.vals })
	;
public set[MId[&F]] run(setmid(set[MId[&F]] vals)) = vals;
public SetMId[&F] liftSetMId(MId[&F] mval) = setmid({ mval });	

@doc{Monad modelling stateful computations}
data StateMId[&F] = statemid(SetMId[tuple[&F, AstNode]] (AstNode) val)
					 ;
public StateMId[&F] inclStateMId(&F val) 
	= statemid(SetMId[tuple[&F, AstNode]] (AstNode t) { return inclSetMId(<val, t>); })
	;
public StateMId[&F1] bind(StateMId[&F] mval, StateMId[&F1] (&F) f)
	= statemid( SetMId[tuple[&F1, AstNode]] (AstNode t) { 
		return setmid( { *( (some(<&F v, AstNode tt>) := run(val)) ? run(run1(tt, f(v))) : { val } ) 
								| MId[tuple[&F, AstNode]] val <- run(mval.val(t)) } ); } )
	;
public StateMId[&F3] bind(StateMId[&F1] mval1, StateMId[&F2] mval2, StateMId[&F3] (&F1, &F2) f) 
	= bind(mval1, StateMId[&F3] (&F1 val1) { return bind(mval2, StateMId[&F3] (&F2 val2) { return f(val1, val2); }); })
	;		
public SetMId[tuple[&F, AstNode]] run1(AstNode t, StateMId[&F] mval) 
	= mval.val(t)
	;
public StateMId[AstNode] fetchMIdSTerm() 
	= statemid(SetMId[tuple[AstNode, AstNode]] (AstNode t) { return inclSetMId(<t, t>); })
	;		
public StateMId[AstNode] assignMIdSTerm(AstNode t) 
	= statemid(SetMId[tuple[AstNode, AstNode]] (AstNode tt) { return inclSetMId(<t, t>); })
	;
@doc{Extra state}
data ConsM[&F] = statemid2(StateMId[&F] (CompilUnit, Mapper) val)
		   ;
public ConsM[&F] inclConsM(&F val) 
	= statemid2(StateMId[&F] (CompilUnit facts, Mapper mapper) { return inclStateMId(val); })
	;
public ConsM[&F1] bind(ConsM[&F] mval, ConsM[&F1] (&F) f)
	= statemid2( StateMId[&F1] (CompilUnit facts, Mapper mapper) {
		return statemid( SetMId[tuple[&F1, AstNode]] (AstNode t) {
			return setmid( { *( (some(<&F v, AstNode tt>) := run(val)) ? run(run1(tt, run(facts, mapper, f(v)))) : { val } )
									| MId[tuple[&F, AstNode]] val <- run(run1(t, mval.val(facts, mapper))) } ); } ); })
	;
public ConsM[&F3] bind(ConsM[&F1] mval1, ConsM[&F2] mval2, ConsM[&F3] (&F1, &F2) f) 
	= bind(mval1, ConsM[&F3] (&F1 val1) { return bind(mval2, ConsM[&F3] (&F2 val2) { return f(val1, val2); }); })
	;		
public StateMId[&F] run(CompilUnit facts, Mapper mapper, ConsM[&F] mval) 
	= mval.val(facts, mapper)
	;
public ConsM[CompilUnit] fetchConsMFacts() 
	= statemid2(StateMId[CompilUnit] (CompilUnit facts, Mapper _) { return inclStateMId(facts); })
	;
public ConsM[Mapper] fetchConsMMapper() 
	= statemid2(StateMId[Mapper] (CompilUnit _, Mapper mapper) { return inclStateMId(mapper); })
	;
@doc{Lifting functions}
public StateMId[&F] liftStateMId(MId[&F] mval) 
	 = statemid(SetMId[tuple[&F, AstNode]] (AstNode t) { 
		return liftSetMId( (some(&F val) := run(mval)) ? inclMId(<val, t>) : bind(bind(fetchv(mval), MId[&F] (&F v) { return inclMId(<v, t>); }), toConst) ); 
	  })
	;
public StateMId[&F] liftStateMId(SetMId[&F] mval) 
	= statemid(SetMId[tuple[&F, AstNode]] (AstNode t) { 
		return bind(mval, SetMId[tuple[&F, AstNode]] (&F v) { return inclSetMId(<v, t>); } ); })
	;
public StateMId[&F] liftStateMId(StateMId[&F] mval) = mval;

public ConsM[&F] liftConsM(MId[&F] mval) 
	= statemid2(StateMId[&F] (CompilUnit facts, Mapper mapper) {
		return liftStateMId(mval); } )
	;
public ConsM[&F] liftConsM(SetMId[&F] mval) 
	= statemid2(StateMId[&F] (CompilUnit facts, Mapper mapper) { 
		return liftStateMId(mval); })
	;
public ConsM[&F] liftConsM(StateMId[&F] mval) 
	= statemid2(StateMId[&F] (CompilUnit facts, Mapper mapper) { return mval; })
	;
public ConsM[&F] liftConsM(ConsM[&F] mval) = mval;
public ConsM[&F] (ConsM[&F]) liftM(MId[&F] (MId[&F]) f) 
	= ConsM[&F] (ConsM[&F] mval) { 
		return statemid2( StateMId[&F] (CompilUnit facts, Mapper mapper) {
			return statemid(SetMId[tuple[&F, AstNode]] (AstNode t) {
				return setmid({ f(val) | MId[tuple[&F, AstNode]] val <-  run(run(t, mval.val(facts, mapper))) }); }); } ); }
	;
public default ConsM[&F] liftConsM(&F val) = inclConsM(val);

@doc{Execute computations}
public set[MId[tuple[&F, AstNode]]] execute(CompilUnit facts, Mapper mapper, AstNode t, ConsM[&F] val) = run(run1(t, run(facts, mapper, val)));

// ----- Bunch of prettyprint utility functions -------------------------------------
public str prettyprint(tuple[&F, AstNode] val) = "(<prettyprint(val[0])>, <prettyprint(val[1])>)";
public str prettyprint(set[&F] vals) = "{ <for(val<-vals){><prettyprint(val)><}> }";
public str prettyprint(typeof(&F val)) = "[<prettyprint(val)>]";
public str prettyprint(typeid(&F val)) = "[<prettyprint(val)>]";
public str prettyprint(settypeof(set[TypeOf[&F]] vals)) = "{ <for(val<-vals){><prettyprint(val)>;<}> }";
public str prettyprint(none()) = "_";
public str prettyprint(some(&F val)) = "<prettyprint(val)>";
public str prettyprint(mid(&F val)) = "[<prettyprint(val)>]";
public str prettyprint(setmid(set[MId[&F]] vals)) = "{ <for(val<-vals){><prettyprint(val)>;<}> }";
public str prettyprint(Constraint[&Mon] c) {
	switch(c) {
		case eq(&Mon lh, &Mon rh): return "<prettyprint(lh)> == <prettyprint(rh)>";
		case subtype(&Mon lh, &Mon rh): return "<prettyprint(lh)> \<: <prettyprint(rh)>";
	}	
}
data AstNode = emptynode();
public str prettyprint(emptynode()) = "emptynode";
