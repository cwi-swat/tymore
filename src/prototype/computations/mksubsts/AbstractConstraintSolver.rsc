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
import Set;


public alias ParamSolutions = map[TypeOf[Entity], SubstsTL_[Entity]];

@doc{
public set[Constraint[TypeOf[Entity]]] solveit(Constraint::eq(TypeOf[Entity] l, TypeOf[Entity] r));
public set[Constraint[TypeOf[Entity]]] solveit(Constraint::subtype(TypeOf[Entity] l, TypeOf[Entity] r));
}

// TODO: also needs to be in a monadic form
public ParamSolutions solutions = ();

// To deal with duplicates
public set[Constraint[SubstsTL[Entity]]] constraints = {};

@doc{EXTENSION with plain generics}
public set[Constraint[SubstsTL[Entity]]] solveit(CompilUnit facts, Mapper mapper, 
												 Constraint::eq(SubstsTL[Entity] lh, SubstsTL[Entity] rh)) {
												 
	bool lhIsTypeArg = isTypeArgument(tauToSubstsT(lh));
	bool rhIsTypeArg = isTypeArgument(tauToSubstsT(rh));
	
	TypeOf[Entity] lv = eval(lh);
	TypeOf[Entity] rv = eval(rh);
		
	// left- and right-hand side are both type argument variables	
	if(lhIsTypeArg && rhIsTypeArg) {
		if(lv in solutions) {		
			solutions[lv] = (rv in solutions) ? intersect(facts, mapper, solutions[lv], solutions[rv], 0) // Note: reverse order!
											  : solutions[lv];
			solutions[rv] = (rv in solutions) ? intersect(facts, mapper, solutions[rv], solutions[lv], 0) 
											  : solutions[lv];
		} else if(rv in solutions) { // Note: lv is not in solutions
			solutions[lv] = solutions[rv];
		}
	// only left-hand side is a type argument variable
	} else if(lhIsTypeArg && !rhIsTypeArg) {		
		solutions[lv] = (lv in solutions) ? intersect(facts, mapper, solutions[lv], tauToSubstsTL_(rh), 0) // Note: reverse order! 
										  : tauToSubstsTL_(rh);								
	// only right-hand side is a type argument variable
	} else if(!lhIsTypeArg && rhIsTypeArg) {	
		solutions[rv] = (rv in solutions) ? intersect(facts, mapper, solutions[rv], tauToSubstsTL_(lh), 0) 
								: tauToSubstsTL_(lh);					
	}
	
	return { Constraint::eq(lh,rh) };			 
}

public set[Constraint[SubstsTL[Entity]]] solveit(CompilUnit facts, Mapper mapper, 
												 Constraint::subtype(SubstsTL[Entity] lh, SubstsTL[Entity] rh)) {
	
	bool lhIsTypeArg = isTypeArgument(tauToSubstsT(lh));
	bool rhIsTypeArg = isTypeArgument(tauToSubstsT(rh));
	
	TypeOf[Entity] lv = eval(lh);
	TypeOf[Entity] rv = eval(rh);
		
	// left- and right-hand side are both type argument variables	
	if(lhIsTypeArg && rhIsTypeArg) {
		if(lv in solutions) {		
			solutions[lv] = (rv in solutions) ? intersectLHS(facts, mapper, solutions[lv], solutions[rv])
											  : solutions[lv];
			solutions[rv] = (rv in solutions) ? intersectRHS(facts, mapper, solutions[lv], solutions[rv]) 
											  : { sups = supertypes_all_(facts, mapper, solutions[lv]);
												  // DEBUG: println("supertype values in Ta \<: Ta: <prettyprint(sups)>"); 
												  sups; };
		} else if(rv in solutions) { // Note: lv is not in solutions
			solutions[lv] = solutions[rv]; // TODO: should be actually subtypes
		}
	// only left-hand side is a type argument variable
	} else if(lhIsTypeArg && !rhIsTypeArg) {
		solutions[lv] = (lv in solutions) ? intersectLHS(facts, mapper, solutions[lv], tauToSubstsTL_(rh)) 
										  : tauToSubstsTL_(rh); // TODO: should be actually subtypes
	// only right-hand side is a type argument variable
	} else if(!lhIsTypeArg && rhIsTypeArg) {
		solutions[rv] = (rv in solutions) ? intersectRHS(facts, mapper, tauToSubstsTL_(lh), solutions[rv]) 
								: { sups = supertypes_all_(facts, mapper, tauToSubstsTL_(lh));
									// DEBUG: println("supertype values of <prettyprint(tauToSubstsTL_(lh))>"); println("supertype values in vT \<: Ta: <prettyprint(sups)>");  
									sups; };
	}
	
	return { Constraint::subtype(lh, rh) };
}

public SubstsTL_[Entity] supertypes_all_(CompilUnit facts, Mapper mapper, SubstsTL_[Entity] mv)
	= tauToSubstsTL_(bind(tauToSubstsT_(mv), SubstsT_[Entity] (Entity v) {
						return supertypes_all(facts, mapper, v); }));

public SubstsTL_[Entity] intersectLHS(CompilUnit facts, Mapper mapper, SubstsTL_[Entity] l, SubstsTL_[Entity] r) {
	SubstsT_[&T] l_ = tauToSubstsT_(l);
	SubstsT_[&T] res = bind(l_, SubstsT_[Entity] (Entity lv) { 
							return bind(tau(popSubsts()), SubstsT_[Entity] (Substs substs) {
										SubstsTL_[Entity] cond = intersectRHS(facts, mapper, 
															   				  tauToSubstsTL_(bind(appnd(substs), SubstsT[Entity] (value _) { 
																									return returnS(lv); })),
															   				  r);				 
										return !isZero(cond) ? returnS_(lv) : lift([]); });
						});
	return tauToSubstsTL_(res);
}

public SubstsTL_[Entity] intersectRHS(CompilUnit facts, Mapper mapper, SubstsTL_[Entity] l, SubstsTL_[Entity] r) {
	return intersect(facts, mapper, r, supertypes_all_(facts, mapper, l), -1);
}

public SubstsTL_[Entity] intersect(CompilUnit facts, Mapper mapper, SubstsTL_[Entity] l, SubstsTL_[Entity] r, int kind) { 
	SubstsTL_[Entity] res = bind(l, SubstsTL_[Entity] (Entity lv) {
								return bind(r, SubstsTL_[Entity] (Entity rv) { 
											return (lv == rv) ? returnSL_(rv) : liftTL_({}); }); });
	return inferMoreTypeArgumentConstraints(facts, mapper, res, kind);
}

public SubstsTL_[Entity] inferMoreTypeArgumentConstraints(CompilUnit facts, Mapper mapper, SubstsTL_[Entity] mvals, int kind) {
	rel[Entity,list[Substs]] vals = run(mvals);
	for(<Entity val, list[Substs] ss> <- vals, size(ss) > 1) {
		Substs first = ss[0];
		ss = delete(ss,0);
		Entity val_i = val; // Attention: to stay safe with the current Rascal semantics for closures!!!
		for(Substs substs <- ss) {
			SubstsT[Entity] lh = bind(appnd(first), SubstsT[Entity] (value _) { 
									return returnS(val_i); });
			Substs substs_i = substs; // Attention: to stay safe with the current Rascal semantics for closures!!!
			SubstsT[Entity] rh = bind(appnd(substs_i), SubstsT[Entity] (value _) { 
									return returnS(val_i); });
									
			set[Constraint[SubstsT[Entity]]] inferred = subtyping(facts, mapper, kind == -1 ? Constraint::subtype(rh,lh) : Constraint::eq(rh,lh));
			
			// Remove the solution if there is a violated constraint
			if(!isEmpty({ c | Constraint[SubstsT[Entity]] c <- inferred, Constraint::violated(_) := c }))
				mvals = bind(mvals, SubstsTL_[Entity] (Entity v) { 
							return (v != val) ? returnSL_(v) : liftTL_({}); } );
			else constraints = constraints + { tauToSubstsTL(c) | Constraint[SubstsT[Entity]] c <- inferred };
		}
	}
	return tauToSubstsTL_(tauToSubstsT_(mvals)); // removes alternative (now under additional constraints) substitutions
}
