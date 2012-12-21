module typecomputations::ConstraintComputations

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;
import lang::java::jdt::refactorings::JDT4Refactorings;
import lang::java::jdt::refactorings::PrettyPrintUtil;

import typecomputations::TypeValues;
import typecomputations::TypeValuesPlusGens;
import typecomputations::SemanticDomains;
import typecomputations::TypeMonadTransformers;
import typecomputations::TypeComputations;
import typecomputations::ConstraintMonadTransformers;
import typecomputations::Constraints;

import Prelude;


public ConsM[&F1] bindinj(ConsM[&F] mval, ConsM[&F1] (TVal[&F]) f) 
	= bind(mval, ConsM[&F1] (&F val) { return bind(f(inj(val)), ConsM[&F1] (&F1 v) { return liftConsM(prjAll(v)); }); })
	;
public ConsM[&F3] bindinj(ConsM[&F1] mval1, ConsM[&F2] mval2, ConsM[&F3] (TVal[&F1], TVal[&F2]) f) 
	= bind(mval1, ConsM[&F3] (&F1 val1) { return bind(mval2, ConsM[&F3] (&F2 val2) { return bind(f(inj(val1), inj(val2)), ConsM[&F3] (&F3 val3) { return liftConsM(prjAll(val3)); }); }); } )
	;
public ConsM[&F] bindXOR(ConsM[&F] mval1, ConsM[&F] mval2) {
	bool nonzero = false;
	bind(mval1, ConsM[&F] (&F val) { nonzero = true; return liftConsM(val); });
	if(nonzero) return mval1;
	return mval2;
}
public ConsM[Constraint[M[PEntity]]] constrain1(wrapval(AstNode t)) 
	= bind(liftConsM(bind(assignMIdSTerm(t), 
					      StateMId[AstNode] (AstNode _) { 
					   			return fetchMIdSTerm(); } )), 
			ConsM[Constraint[M[PEntity]]] (AstNode tt) { return liftConsM(setmid(constrain(tt))); } )
	;
public ConsM[Constraint[M[PEntity]]] constrain2(wrapval(AstNode t)) 
	= bind(liftConsM(bind(assignMIdSTerm(t), 
					      StateMId[AstNode] (AstNode _) { 
					   	  		return fetchMIdSTerm(); } )), 
		   ConsM[Constraint[M[PEntity]]] (AstNode _) {
					return bind(liftConsM(fetchConsMFacts),
					  			ConsM[Constraint[M[PEntity]]] (CompilUnit facts) {
					  			  		return bind(liftConsM(fetchConsMMapper), 
					  			  			  		ConsM[Constraint[M[PEntity]]] (Mapper mapper) {
					  			  							return liftConsM(setmid(constrain(facts, mapper, t))); }); }); })
	;
public ConsM[Constraint[M[PEntity]]] cconstrain(wrapval(AstNode t)) 
	= bindXOR(constrain1(inj(t)), constrain2(inj(t)))
	;

public default ConsM[Constraint[M[PEntity]]] constrain1(TVal[AstNode] val) = constrain1(prj(val));
public default ConsM[Constraint[M[PEntity]]] constrain2(TVal[AstNode] val) = constrain2(prj(val));
public default ConsM[Constraint[M[PEntity]]] cconstrain(TVal[AstNode] val) = cconstrain(prj(val));