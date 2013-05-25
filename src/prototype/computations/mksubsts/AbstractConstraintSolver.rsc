@license{
  Copyright (c) 2009-2011 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - A.Izmaylova@cwi.nl}
module prototype::computations::mksubsts::AbstractConstraintSolver

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::JDT;
import prototype::lang::java::jdt::refactorings::Java;
import prototype::lang::java::jdt::refactorings::JavaADT;
import prototype::lang::java::jdt::refactorings::JavaADTVisitor;
import prototype::lang::java::jdt::refactorings::JDT4Refactorings;
import prototype::lang::java::jdt::refactorings::PrettyPrintUtil;
import prototype::lang::java::jdt::refactorings::ValuesUtil;

import prototype::computations::mksubsts::ConstraintComputation;
import prototype::computations::mksubsts::ConstraintInference;
import prototype::computations::mksubsts::LanguageInterface;
import prototype::computations::mksubsts::Monads;
import prototype::computations::mksubsts::TypeComputation;
import prototype::computations::mksubsts::FunctionsOfTypeValues;

import IO;
import List;


public alias ParamSolutions = map[TypeOf[Entity], SubstsTL_[Entity]];

@doc{
public set[Constraint[TypeOf[Entity]]] solveit(Constraint::eq(TypeOf[Entity] l, TypeOf[Entity] r));
public set[Constraint[TypeOf[Entity]]] solveit(Constraint::subtype(TypeOf[Entity] l, TypeOf[Entity] r));
}

// TODO: also need to be formulated in a monadic way
public ParamSolutions solutions = ();
public set[Constraint[SubstsTL[Entity]]] constraints = {};

@doc{EXTENSION with plain generics}
public set[Constraint[SubstsTL[Entity]]] solveit(CompilUnit facts, Mapper mapper, 
												 Constraint::eq(SubstsTL[Entity] lh, SubstsTL[Entity] rh)) 
	= { Constraint::eq(lh,rh) };
public set[Constraint[SubstsTL[Entity]]] solveit(CompilUnit facts, Mapper mapper, 
												 Constraint::subtype(SubstsTL[Entity] lh, SubstsTL[Entity] rh)) {
											
	TypeOf[Entity] lv = eval(lh);
	TypeOf[Entity] rv = eval(rh);
	
	bool lhIsTypeArg = isTypeArgument(lh);
	bool rhIsTypeArg = isTypeArgument(rh);
	
	// left- and right-hand side are both type argument variables	
	if(lhIsTypeArg && rhIsTypeArg) {
		if(lv in solutions) {		
			solutions[lv] = (rv in solutions) ? intersectLHS(facts, mapper, solutions[lv], solutions[rv]) : solutions[lv];
			solutions[rv] = (rv in solutions) ? intersectRHS(facts, mapper, solutions[lv], solutions[rv]) 
											  : { sups = supertypes_all_(facts, mapper, solutions[lv]);
											  	  // DEBUG: println("supertype values in Ta \<: Ta: <prettyprint(sups)>"); 
											      sups; };
		} else if(rv in solutions) {
			solutions[lv] = (lv in solutions) ? intersectLHS(facts, mapper, solutions[lv], solutions[rv]) : solutions[lv];
			solutions[rv] = (lv in solutions) ? intersectRHS(facts, mapper, solutions[lv], solutions[rv]) 
											  : solutions[rv]; // TODO: should be actually subtypes
		}
	// only left-hand side is a type argument variable
	} else if(lhIsTypeArg && !rhIsTypeArg) {
		solutions[lv] = (lv in solutions) ? intersectLHS(facts, mapper, solutions[lv], tauToSubstsTL_(rh)) : tauToSubstsTL_(rh);
	// only right-hand side is a type argument variable
	} else if(!lhIsTypeArg && rhIsTypeArg) {
		solutions[rv] = (rv in solutions) ? intersectRHS(facts, mapper, tauToSubstsTL_(lh), solutions[rv]) 
											  : { sups = supertypes_all_(facts, mapper, tauToSubstsTL_(lh));
											  	  // DEBUG: println("supertype values of <prettyprint(tauToSubstsTL_(lh))>"); println("supertype values in vT \<: Ta: <prettyprint(sups)>");  
											  	  sups; };
	}
	
	return { Constraint::subtype(lh, rh) };
}

public bool isTypeArgument(SubstsTL[Entity] v) = !isZero(bind(v, SubstsTL[Entity] (Entity v_) { return isTypeArgument(v_) ? returnSL(v_) : liftTL(tzero()); }));

@doc{Computes all the supertypes; assumes that values are type values in their generic form}
public SubstsT_[Entity] supertypes_all(CompilUnit facts, Mapper mapper, Entity v) {
	return bind(isEmpty(getTypeParamsOrArgs(v)) ? discard(returnS_(v)) : returnS_(v), SubstsT_[Entity] (Entity v) {
				return concat(returnS_(v), 
				   	   bind(lift(supertypes(facts, v)), SubstsT_[Entity] (Entity vS) {
							return bind(tau(pushSubsts(paramSubstsWith(mapper, inherits(getGenV(mapper, v), vS)))(mapper, vS)), SubstsT_[Entity] (Entity _) {
										return supertypes_all(facts, mapper, getGenV(mapper, vS)); }); })); });
}

public SubstsTL_[Entity] supertypes_all_(CompilUnit facts, Mapper mapper, SubstsTL_[Entity] mv)
	= tauToSubstsTL_(bind(tauToSubstsT_(mv), SubstsT_[Entity] (Entity v) {
						return supertypes_all(facts, mapper, v); }));

public SubstsTL_[Entity] intersectLHS(CompilUnit facts, Mapper mapper, SubstsTL_[Entity] l, SubstsTL_[Entity] r) {
	return bind(l, SubstsTL_[Entity] (Entity lv) { 
				SubstsTL_[Entity] cond = intersectRHS(facts, mapper, returnSL_(lv), r);
				return !isZero(cond) ? returnSL_(lv) : liftTL_({});
			});
}

public SubstsTL_[Entity] intersectRHS(CompilUnit facts, Mapper mapper, SubstsTL_[Entity] l, SubstsTL_[Entity] r) {
	return intersect(supertypes_all_(facts, mapper, l),r);
}

public SubstsTL_[Entity] intersect(SubstsTL_[Entity] l, SubstsTL_[Entity] r) 
	= bind(l, SubstsTL_[Entity] (Entity lv) {
				return bind(r, SubstsTL_[Entity] (Entity rv) { 
							return (lv == rv) ? returnSL_(rv) : liftTL_({}); }); });
