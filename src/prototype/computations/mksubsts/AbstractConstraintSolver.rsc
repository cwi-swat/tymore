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
import prototype::computations::mksubsts::BoundSemWithoutWildCards0;
import prototype::computations::mksubsts::BoundSemWithWildCards0;
import prototype::computations::mksubsts::LanguageInterface;
import prototype::computations::mksubsts::Monads;
import prototype::computations::mksubsts::TypeComputation;
import prototype::computations::mksubsts::FunctionsOfTypeValues;

import Type;

import IO;
import List;
import Map;
import Relation;
import Set;


public alias ParamSolutions = map[SubstsTL[Entity], SubstsTL_[Entity]];

@doc{
public set[Constraint[TypeOf[Entity]]] solveit(Constraint::eq(TypeOf[Entity] l, TypeOf[Entity] r));
public set[Constraint[TypeOf[Entity]]] solveit(Constraint::subtype(TypeOf[Entity] l, TypeOf[Entity] r));
}

public ParamSolutions solutions = ();

// To deal with duplicates
public set[Constraint[SubstsTL[Entity]]] constraints = {};

@doc{EXTENSION with plain generics}
public set[Constraint[SubstsTL[Entity]]] solveit(CompilUnit facts, Mapper mapper, 
												 Constraint::eq(SubstsTL[Entity] lh, SubstsTL[Entity] rh), 
												 bool allConstraints = true) {
	
	Constraint[SubstsTL[Entity]] c = Constraint::eq(lh,rh);
												 
	bool lhIsTypeArg = isTypeArgument(lh);
	bool rhIsTypeArg = isTypeArgument(rh);
	
	// (1) left- and right-hand side are both type argument variables	
	if(lhIsTypeArg && rhIsTypeArg) {
		if(lh in solutions) {		
			solutions[lh] = (rh in solutions) ? intersect(facts, mapper, c, solutions[lh], solutions[rh])
											  : solutions[lh];
			solutions[rh] = (rh in solutions) ? intersect(facts, mapper, c, solutions[rh], solutions[lh]) // Note: reverse order! 
											  : solutions[lh];
		} else if(rh in solutions) { // Note: lh is not in solutions
			solutions[lh] = solutions[rh];
		}
	// (2) only left-hand side is a type argument variable
	} else if(lhIsTypeArg && !rhIsTypeArg) {		
		solutions[lh] = (lh in solutions) ? intersect(facts, mapper, c, solutions[lh], tauToSubstsTL_(rh)) 
										  : tauToSubstsTL_(rh);								
	// (3) only right-hand side is a type argument variable
	} else if(!lhIsTypeArg && rhIsTypeArg) {	
		solutions[rh] = (rh in solutions) ? intersect(facts, mapper, c, solutions[rh], tauToSubstsTL_(lh)) // Note: reverse order! 
								          : tauToSubstsTL_(lh);					
	}
	
	return { Constraint::eq(lh,rh) };			 
}

public set[Constraint[SubstsTL[Entity]]] solveit(CompilUnit facts, Mapper mapper, 
												 Constraint::subtype(SubstsTL[Entity] lh, SubstsTL[Entity] rh), 
												 bool allConstraints = true) {
	
	Constraint[SubstsTL[Entity]] c = Constraint::subtype(lh,rh);
	
	bool lhIsTypeArg = isTypeArgument(lh);
	bool rhIsTypeArg = isTypeArgument(rh);
	
	// (1) left- and right-hand side are both type argument variables	
	if(lhIsTypeArg && rhIsTypeArg) {
		if(lh in solutions) {		
			solutions[lh] = (rh in solutions) ? intersectLHS(facts, mapper, c, solutions[lh], solutions[rh])
											  : solutions[lh];
			solutions[rh] = (rh in solutions) ? intersectRHS(facts, mapper, c, solutions[lh], solutions[rh]) 
											  : intersectRHS(facts, mapper, c, solutions[lh]); // the case of an uninitialized variable (universe solution)
		} else if(rh in solutions) { // Note: lh is not in solutions
			if(allConstraints)
				solutions[lh] = intersectLHS(facts, mapper, c, solutions[rh]);
		}
	// (2) only left-hand side is a type argument variable
	} else if(lhIsTypeArg && !rhIsTypeArg) {
		if(lh in solutions || allConstraints)
			solutions[lh] = (lh in solutions) ? intersectLHS(facts, mapper, c, solutions[lh], tauToSubstsTL_(rh))
										  	  : intersectLHS(facts, mapper, c, tauToSubstsTL_(rh));
	// (3) only right-hand side is a type argument variable
	} else if(!lhIsTypeArg && rhIsTypeArg) {
		solutions[rh] = (rh in solutions) ? intersectRHS(facts, mapper, c, tauToSubstsTL_(lh), solutions[rh]) 
								          : intersectRHS(facts, mapper, c, tauToSubstsTL_(lh));								
	}
	
	return { c };
}

// public SubstsTL_[Entity] intersectLHS(CompilUnit facts, Mapper mapper, Constraint[SubstsTL[Entity]] c, SubstsTL_[Entity] r) = r;
@doc{EXTENSION with wildcards: memo}
public map[tuple[SubstsTL_[Entity],SubstsTL[Entity],Constraint[SubstsTL[Entity]]],SubstsTL_[Entity]] memoIntersectLHS1 = ();
@doc{EXTENSION with wildcards: intersectLHS}
public SubstsTL_[Entity] intersectLHS(CompilUnit facts, Mapper mapper, Constraint[SubstsTL[Entity]] c, SubstsTL_[Entity] r) {
	if(<r,c.lh,c> in memoIntersectLHS1) return memoIntersectLHS1[<r,c.lh,c>];

	SubstsT_[Entity] l = bind(tau(tauToSubstsT(c.lh)), SubstsT_[Entity] (Entity var) {
							  SubstsT_[Entity] b = lift([]);
							  if(isLowerBoundTypeArgument(var))
							  		b = returnS_(entity([ bottom() ])); // ***Note: in case of lower bounds, adds a bottom type to possible values
							  return concat(b, bind(tauToSubstsT_(r), SubstsT_[Entity] (Entity val) {
													return tau(replaceSubsts(facts, mapper, val, var)); })); });
	
	res = intersectLHS(facts, mapper, c, tauToSubstsTL_(l), r);

	memoIntersectLHS1[<r,c.lh,c>] = res;
	return res;
}

public map[tuple[SubstsTL_[Entity],SubstsTL_[Entity],Constraint[SubstsTL[Entity]]],SubstsTL_[Entity]] memoIntersectLHS2 = ();
public default SubstsTL_[Entity] intersectLHS(CompilUnit facts, Mapper mapper, Constraint[SubstsTL[Entity]] c, SubstsTL_[Entity] l, SubstsTL_[Entity] r) {
	if(<l,r,c> in memoIntersectLHS2) return memoIntersectLHS2[<l,r,c>];
	
	// 'intersectLHS' in terms of 'intersectRHS'
	SubstsTL_[Entity] res = bind(l, SubstsTL_[Entity] (Entity lv) {
								SubstsTL_[Entity] l_ = bind(l, SubstsTL_[Entity] (Entity lv_) {
															return (lv == lv_) ? returnSL_(lv_) : liftTL_({}); });
								SubstsTL_[Entity] cond = intersectRHS(facts, mapper, c, l_, r);
								return !isZero(cond) ? returnSL_(lv) : liftTL_({}); });

	memoIntersectLHS2[<l,r,c>] = res;
	return res;
}

@doc{The case when rhs is an uninitialized variable (universe solution)}
// public map[SubstsTL_[Entity],SubstsTL_[Entity]] memoIntersectRHS1 = ();
//public SubstsTL_[Entity] intersectRHS(CompilUnit facts, Mapper mapper, Constraint[SubstsTL[Entity]] c, SubstsTL_[Entity] l) {
//	if(l in memoIntersectRHS1) return memoIntersectRHS1[l];
//																   
//	res = supertypes_all_(facts, mapper, l);
//	
//	memoIntersectRHS1[l] = res;
//	return res;
//}
@doc{EXTENSION with wildcards}
public map[tuple[SubstsTL_[Entity],SubstsTL[Entity],Constraint[SubstsTL[Entity]]],SubstsTL_[Entity]] memoIntersectRHS1 = ();
@doc{EXTENSION with wildcards}
public SubstsTL_[Entity] intersectRHS(CompilUnit facts, Mapper mapper, Constraint[SubstsTL[Entity]] c, SubstsTL_[Entity] l) {
	if(<l,c.rh,c> in memoIntersectRHS1) return memoIntersectRHS1[<l,c.rh,c>];
																   
	res = intersect(facts, mapper, c, _supertypes_all_(facts, mapper, l, c.rh), supertypes_all_(facts, mapper, l)); // the second argument is exactly the super

	memoIntersectRHS1[<l,c.rh,c>] = res;
	return res;
}

public map[tuple[SubstsTL_[Entity],SubstsTL_[Entity],Constraint[SubstsTL[Entity]]],SubstsTL_[Entity]] memoIntersectRHS2 = ();
//public default SubstsTL_[Entity] intersectRHS(CompilUnit facts, Mapper mapper, Constraint[SubstsTL[Entity]] c, SubstsTL_[Entity] l, SubstsTL_[Entity] r) {
//	if(<l,r> in memoIntersectRHS2) return memoIntersectRHS2[<l,r>];
//	
//	SubstsTL_[Entity] res = intersect(facts, mapper, c, r, supertypes_all_(facts, mapper, l));
//	
//	memoIntersectRHS2[<l,r>] = res;
//	return res;
//}
@doc{EXTENSION with wildcards}
public default SubstsTL_[Entity] intersectRHS(CompilUnit facts, Mapper mapper, Constraint[SubstsTL[Entity]] c, SubstsTL_[Entity] l, SubstsTL_[Entity] r) {
	if(<l,r,c> in memoIntersectRHS2) return memoIntersectRHS2[<l,r,c>];
	
	if(entity([ bottom() ]) in eval(l)) return r; // identity behaviour if the left-hand side set has a bottom type
	
	SubstsTL_[Entity] res = intersect(facts, mapper, c, r, supertypes_all_(facts, mapper, l));
	
	memoIntersectRHS2[<l,r,c>] = res;
	return res;
}


@doc{EXTENSION with wildcards}
public SubstsT[Entity] replaceSubsts(CompilUnit facts, Mapper mapper, Entity val, Entity var) {
	list[Entity] params = getTypeParamsOrArgs(val);
	if(isEmpty(params) || !isTypeArgument(var))
		return returnS(val);
	return bind(popSubsts(), SubstsT[Entity] (Substs s) {
				Substs repl = ( substs([],[]) | concat(it, s_) 
											  | Entity param <- params, 
												Entity arg := lookupSubsts(s, param),
												arg != zero(),
												Substs s_ := substs([ replaceTypeArgumentContext(arg, param, var) ], 
														 		 	[ param ]) );
				return bind(appnd(repl), SubstsT[Entity] (value _) {
							return returnS(val); }); });
}

public Entity replaceTypeArgumentContext(Entity \type, Entity param, Entity ctx) {
	bool captured = false;
	if(entity([ *_, captured(Entity cctx)]) := ctx) {
		captured = true;
		ctx = cctx;
	}
	if(isTypeArgument(\type)) {
		if(isCapturedTypeArgument(\type) && captured)
			return entity([ captureof(entity([ typeArgument(\type.id[0].wildCard.id[0].name, ctx, zero()) ])) ]);
		if(isCapturedTypeArgument(\type) && !captured)
			return entity([ typeArgument(\type.id[0].wildCard.id[0].name, ctx, zero()) ]);
		if(captured)
			return entity([ captureof(entity([ typeArgument(\type.id[0].name, ctx, zero()) ])) ]);
		return entity([ typeArgument(\type.id[0].name, ctx, zero()) ]);
	}
	if(captured)
		entity([ captureof(entity([ typeArgument(param.id[0].name, ctx, zero()) ])) ]);
	return entity([ typeArgument(param.id[0].name, ctx, zero()) ]);
}

@doc{Computes ***all*** the supertypes; ***note: it assumes that the input value is a type value in its generic form}
public SubstsT_[Entity] supertypes_all(CompilUnit facts, Mapper mapper, Entity v) {
	return bind(isEmpty(getTypeParamsOrArgs(v)) ? discard(returnS_(v)) : returnS_(v), SubstsT_[Entity] (Entity v) {	
				return concat(returnS_(v), 
				   	   		  bind(lift(supertypes(facts, v)), SubstsT_[Entity] (Entity vS) {
				   	   				if(v in getTypeParamsOrArgs(vS)) // takes care of cycling
				   	   					return lift([]);
				   	   				return bind(tau(pushSubsts(paramSubstsWith(facts, mapper, inherits(getGenV(facts, mapper, v), vS)))(facts, mapper, vS)), SubstsT_[Entity] (Entity _) {
												return supertypes_all(facts, mapper, getGenV(facts, mapper, vS)); }); })); });
}

@doc{EXTENSION with wildcards}
public SubstsT_[Entity] _supertypes_all(CompilUnit facts, Mapper mapper, Entity v, Entity var) {
	// New substitution related aspect add to the recursive supertypes call 
	// Introduces new type argument variables, if necessary, before computing supertypes
	SubstsT_[Entity] mv = tau(replaceSubsts(facts, mapper, v, var));
	// The rest is the super
	return bind(mv, SubstsT_[Entity] (Entity v) {
				return bind(isEmpty(getTypeParamsOrArgs(v)) ? discard(returnS_(v)) : returnS_(v), SubstsT_[Entity] (Entity v) {	
							return concat(returnS_(v), 
				   	   					  bind(lift(supertypes(facts, v)), SubstsT_[Entity] (Entity vS) {
				   	   							if(v in getTypeParamsOrArgs(vS)) // takes care of possible cycling dependencies
				   	   								return lift([]);
				   	   							return bind(tau(pushSubsts(paramSubstsWith(facts, mapper, inherits(getGenV(facts, mapper, v), vS)))(facts, mapper, vS)), SubstsT_[Entity] (Entity _) {
															return _supertypes_all(facts, mapper, getGenV(facts, mapper, vS), var); }); })); }); });
}

@doc{Subtypes semantics; assumes generic type values}
public SubstsT_[Entity] subtypes(CompilUnit facts, Mapper mapper, Entity v) { 
	lrel[Entity,Substs] subs = [ <psub.genval, psup.s> 
										| <Entity sub, Entity sup> <- facts["supertypes_func"], 
										  psup := mkSubsts(facts, mapper, sup), 
										  psup.genval == v,
										  psub := mkSubsts(facts, mapper, sub),
										  psub.genval == sub ]; // subtype in a generic form
	if(isEmpty(getTypeParamsOrArgs(v)))
		subs = [ <sub,substs> | <sub,substs> <- subs, isEmpty(getTypeParamsOrArgs(sub)) ];
	res = bind(lift(subs), SubstsT_[Entity] (tuple[Entity v,Substs substs] sup) {
				return tau(bind(appnd(sup.substs), SubstsT[Entity] (value _) { 
								return returnS(sup.v); })); });
	return res;
}

public map[SubstsTL_[Entity],SubstsTL_[Entity]] memoSupertypes = ();
public SubstsTL_[Entity] supertypes_all_(CompilUnit facts, Mapper mapper, SubstsTL_[Entity] mv) {
	if(mv in memoSupertypes) return memoSupertypes[mv];
	
	SubstsTL_[Entity] res = tauToSubstsTL_(bind(tauToSubstsT_(mv), SubstsT_[Entity] (Entity v) {
												SubstsT_[Entity] sups = supertypes_all(facts, mapper, v);
												return sups; }));
	memoSupertypes[mv] = res;
	return res;
}

@doc{EXTENSION with wildcards}
public map[tuple[SubstsTL_[Entity],SubstsTL[Entity]],SubstsTL_[Entity]] _memoSupertypes = ();
@doc{EXTENSION with wildcards}
public SubstsTL_[Entity] _supertypes_all_(CompilUnit facts, Mapper mapper, SubstsTL_[Entity] mv, SubstsTL[Entity] var) {
	if(<mv,var> in _memoSupertypes) return _memoSupertypes[<mv,var>];
	
	SubstsTL_[Entity] res = tauToSubstsTL_(bind(tau(lift(eval(var))), SubstsT_[Entity] (Entity varv) {
												return bind(tauToSubstsT_(mv), SubstsT_[Entity] (Entity v) {
															SubstsT_[Entity] sups = _supertypes_all(facts, mapper, v, varv);
															return sups; }); }));
	_memoSupertypes[<mv,var>] = res;
	return res;
}

public map[tuple[SubstsTL_[Entity],SubstsTL_[Entity],Constraint[SubstsTL[Entity]]],SubstsTL_[Entity]] memoIntersect = ();
public SubstsTL_[Entity] intersect(CompilUnit facts, Mapper mapper, Constraint[SubstsTL[Entity]] c, SubstsTL_[Entity] l, SubstsTL_[Entity] r) { 
	if(<l,r,c> in memoIntersect) return memoIntersect[<l,r,c>];
	
	SubstsTL_[Entity] res = bind(l, SubstsTL_[Entity] (Entity lv) {
								return bind(r, SubstsTL_[Entity] (Entity rv) { 
											return (lv == rv) ? returnSL_(rv) : liftTL_({}); }); });
	
	res_ = inferMoreTypeArgumentConstraints(facts, mapper, c, res);
	
	memoIntersect[<l,r,c>] = res_;

	return res_;
}

public map[tuple[Entity,list[Substs],Constraint[SubstsTL[Entity]]],set[Constraint[SubstsT[Entity]]]] memoInference = ();
public SubstsTL_[Entity] inferMoreTypeArgumentConstraints(CompilUnit facts, Mapper mapper, Constraint[SubstsTL[Entity]] c, SubstsTL_[Entity] mvals) {
	rel[Entity,list[Substs]] vals = run(mvals);
	for(<Entity val, list[Substs] ss0> <- vals, size(ss0) > 1) {
		Substs first = ss0[0];
		ss = delete(ss0,0);
		Entity val_i = val; // Attention: to stay safe with the current Rascal semantics for closures!!!
		for(Substs substs <- ss) {
			Substs substs_i = substs; // Attention: to stay safe with the current Rascal semantics for closures!!!
			SubstsT[Entity] lh = bind(appnd(substs_i), SubstsT[Entity] (value _) { 
									return returnS(val_i); });
			SubstsT[Entity] rh = bind(appnd(first), SubstsT[Entity] (value _) { 
									return returnS(val_i); });						
			set[Constraint[SubstsT[Entity]]] inferred = {};
			if(<val,ss0,c> in memoInference) { 
				inferred = memoInference[<val,ss0,c>];
			} else {
				inferred = subtyping(facts, mapper, Constraint::subtype(_,_) := c ? Constraint::subtype(lh,rh) : Constraint::eq(lh,rh));
				memoInference[<val,ss0,c>] = inferred;
			}			
			// Remove the solution if there is a violated constraint
			if(!isEmpty({ c | Constraint[SubstsT[Entity]] c <- inferred, Constraint::violated(_) := c })) {
				// DEBUG:
				println("Violated type argument constraint: <prettyprint(val_i)>");
				mvals = bind(mvals, SubstsTL_[Entity] (Entity v) { 
							return (v != val_i) ? returnSL_(v) : liftTL_({}); } );
			}
			else constraints = constraints + { tauToSubstsTL(c) | Constraint[SubstsT[Entity]] c <- inferred };
		}
	}
	SubstsTL_[Entity] res = tauToSubstsTL_(tauToSubstsT_(mvals));
	return res; // removes alternative (now under additional constraints) substitutions
}

@doc{EXTENSION with wildcards}
public bool ifLowerBoundsInferred(CompilUnit facts, Mapper mapper, bool allConstraints = true) {
	set[Constraint[SubstsTL[Entity]]] more =
		{ *c | SubstsTL[Entity] mvar <- solutions,
			   isLowerBoundTypeArgument(mvar), // look up a lower bound type argument variable
			   SubstsTL_[Entity] lsolutions := solutions[mvar], 
			   SubstsTL[Entity] upper := bind(mvar, SubstsTL[Entity] (Entity v) { 
						   						return returnSL(replaceWithUpper(v)); }), // introduce the upper bound type argument variable
			   // First option: checks if the lower bound solution does not have a bottom type, i.e., it has to be specified; 
			   // if yes, tries to equalize the lower and upper bounds
			   set[Constraint[SubstsTL[Entity]]] c 
			   			:= ( (allConstraints && !hasBottom(lsolutions)) 
			   					? { Constraint::eq(mvar,upper), *( (capOfUpper := tauToSubstsTL(bind(tauToSubstsT(upper), SubstsT[Entity] (Entity ub) { 
			   															   							 return capture(facts, mapper, ub); })) && capOfUpper in solutions) 
			   															? { Constraint::eq(capOfUpper, upper) } 
			   															: {} ) }
			   					: { (Constraint::eq(mvar,upper) notin constraints) 
			   							? { Constraint::subtype(mvar,upper) } 
			   							: { (capOfUpper := tauToSubstsTL(bind(tauToSubstsT(upper), SubstsT[Entity] (Entity ub) { 
			   															   	   return capture(facts, mapper, ub); })) && capOfUpper in solutions) 
			   									? { Constraint::eq(capOfUpper, upper) } 
			   									: {}; }; } ),
			    // Second option: checks if the lower bound solution does not have a bottom type, i.e., it has to be specified;
			    // if yes, tries to equalize the upper bound of a wildcard type with the upper bound of the respective type parameter;
			    //set[Constraint[SubstsTL[Entity]]] c 
			    //		:= ( (allConstraints && !hasBottom(lsolutions)) 
			    //				? ( ( Constraint::eq(mvar,upper) notin constraints) 
			    //						? {
			   	//							bool cond =isZero(bind(mvar, SubstsTL[Entity] (Entity var) {
			   	//													return (entity([ *_, typeArgument(_,tuple[str,str] cntx,_), lower(_) ]) := var) ? liftTL(tzero()) : returnSL(var); }));
			   	//							SubstsTL[Entity] b = bind(upper, SubstsTL[Entity] (Entity v) { 
		  	  // 															return tauToSubstsTL(bind(boundEnvWithNoCapture(facts, mapper, getTypeParameter(v)), SubstsT[Entity] (Entity bv) {
		  	  // 																						return returnS(getGenV(facts, mapper, bv)); })); });
		  	  // 								if(cond) println("New equality due to type argument context: <prettyprint(mvar)>; <prettyprint(Constraint::eq(mvar,upper))>");
		  	  // 								cond ? { Constraint::eq(mvar,upper) } : { println("New equality due to upper bound: <prettyprint(Constraint::eq(upper,b))>"); { Constraint::subtype(mvar,upper), Constraint::eq(upper,b) }; };
			   	//						  } 
			   	//						: { (capOfUpper := tauToSubstsTL(bind(tauToSubstsT(upper), SubstsT[Entity] (Entity ub) { 
			   	//														   		return capture(facts, mapper, ub); })) && capOfUpper in solutions) 
			   	//														   					? { Constraint::eq(capOfUpper, upper) } 
			   	//														   					: {}; } )
			   	//				: { Constraint::subtype(mvar,upper) } ),
			  _ := ( (c notin constraints) ? { constraints = constraints + { *c }; solveit(facts, mapper, allConstraints = allConstraints); }
			  						       : { // DEBUG:
			  							       println("Extra equality constraint is already there.");
			  							       {}; })
			  
		} 
		+ 
		addTypeParameterBoundConstraints(facts, mapper, allConstraints = allConstraints);
		
	if(isEmpty(more))
		return false; 

	return true;
}

//public set[Constraint[SubstsTL[Entity]]] addTypeParameterBoundConstraints(CompilUnit facts, Mapper mapper, bool allConstraints = true) {
//	return { c
//		| SubstsTL[Entity] mvar <- solutions,
//		  isTypeArgument(mvar),
//		  SubstsTL[Entity] b := bind(mvar, SubstsTL[Entity] (Entity v) { 
//		  							return tauToSubstsTL(bind(boundEnv(facts, mapper, getTypeParameter(v)), SubstsT[Entity] (Entity bv) {
//		  													return (bv == object()) ? lift(tzero()) : returnS(getGenV(facts, mapper, bv)); })); }),
//		  !isZero(b),
//		  Constraint[SubstsTL[Entity]] c := Constraint::subtype(mvar, b),
//		  c notin constraints,
//		  _ := { constraints = constraints + {c}; solveit(facts, mapper, allConstraints = allConstraints); {}; }
//	};
//}
@doc{EXTENSION with wildcards}
public set[Constraint[SubstsTL[Entity]]] addTypeParameterBoundConstraints(CompilUnit facts, Mapper mapper, bool allConstraints = true) {
	return { c
		| SubstsTL[Entity] mvar <- solutions,
		  isUpperBoundTypeArgument(mvar), // plug here
		  SubstsTL[Entity] b := bind(mvar, SubstsTL[Entity] (Entity v) { 
		  							return tauToSubstsTL(bind(boundEnvWithNoCapture(facts, mapper, getTypeParameter(v)), SubstsT[Entity] (Entity bv) { // plug here
		  													return (bv == object()) ? lift(tzero()) : returnS(getGenV(facts, mapper, bv)); })); }),
		  !isZero(b),
		  Constraint[SubstsTL[Entity]] c := Constraint::subtype(mvar, b),
		  c notin constraints,
		  _ := { constraints = constraints + {c}; solveit(facts, mapper, allConstraints = allConstraints); {}; }
	};
}

public bool hasBottom(SubstsTL_[Entity] mvals) = !isZero(bind(mvals, SubstsTL_[Entity] (Entity val) {
															  return isBottom(val) ? returnSL_(val) : liftTL_({}); }));

public bool solveit(CompilUnit facts, Mapper mapper, bool allConstraints = true) {
	int n = size(constraints);
	solve(solutions, n) {
		println("solve: size == <size(constraints)>; allConstraints == <allConstraints>; ...");
		set[Constraint[SubstsTL[Entity]]] constrs = constraints;
		{ *solveit(facts, mapper, c, allConstraints = allConstraints) | Constraint[SubstsTL[Entity]] c <- constrs };
		n = size(constraints);
	}
	return true;
}

// =========== Choosing one possible solution ===========

@doc{One solution needs to be chosen}
public map[SubstsTL[Entity],str] pp = ();
public void chooseOneSolution(CompilUnit facts, Mapper mapper) {
	println("size of solutions: <size(solutions)>; <size(toRel(solutions))>");
	for(SubstsTL[Entity] var <- solutions, !isCapturedTypeArgument(var)) {
		prettyprintOneSolution(facts, mapper, var);
	}
	tracer(true, "One solution: \n <for(var<-pp){><prettyprint(var)> = <pp[var]>\n<}>");
	tracer(true, "More relevant part of the solution: \n <for(var<-pp,!isLowerBoundTypeArgument(var)&&!isUpperBoundTypeArgument(var)){><prettyprint(var)> = <pp[var]>\n<}>");
}

@doc{Prettyprint one possible solution}
//public str prettyprintOneSolution(CompilUnit facts, Mapper mapper, SubstsTL[Entity] var) {
//	if(!isTypeArgument(var)) 
//		return "<prettyprint(var)>";
//	
//	str vpp = pp[var] ? "";	
//	
//	if(vpp != "") return vpp;
//	
//	rel[Entity,list[Substs]] b = run(solutions[var]);
//	rel[Entity,list[Substs]] bOnes = {<zero(),[]>};
//	list[str] varpps = [];
//		
//	if(vpp == "") {		
//		if(!isEmpty(b)) {
//			bOnes = pickTheMostSpecific(facts, mapper, b);
//			for(tuple[Entity,list[Substs]] bOne<-bOnes) {
//				list[str] bArgs = [];
//				bArgs = [ prettyprintOneSolution(facts, mapper, returnSL(lookupSubsts(bOne[1][0], param))) 
//								| Entity param <- getTypeParamsOrArgs(bOne[0]) ];
//				varpps = varpps + ["<prettyprint(bOne[0])> [<for(arg<-bArgs){><arg>;<}>]"];
//			}
//		}
//	}
//	
//	if(!isEmpty(varpps)) {
//		varpps0 = varpps - ["Serializable []", "Cloneable []"]; // annoying ones, always pops up
//		if(!isEmpty(varpps0)) {
//			varpps = varpps0;
//		}
//		pp[var] = varpps[0];
//		return pp[var];
//	}
//	
//	return "_";
//	
//}
@doc{EXTENSION with wildcards}
public str prettyprintOneSolution(CompilUnit facts, Mapper mapper, SubstsTL[Entity] var) {
	if(!isTypeArgument(var)) 
		return "<prettyprint(var)>";
	
	SubstsTL[Entity] lvar = liftTL(tzero());
	SubstsTL[Entity] uvar = liftTL(tzero());
	SubstsTL[Entity] luvar = liftTL(tzero());
		
	if(isLowerBoundTypeArgument(var)) {
		lvar = var;
		uvar = bind(var, SubstsTL[Entity] (Entity v) { return returnSL(replaceWithUpper(v)); });		
		luvar = bind(lvar, SubstsTL[Entity] (Entity v) { return (entity([ *ids, lower(_) ]) := v) ? returnSL(entity(ids)) : liftTL(tzero()); });
	}	
	if(isUpperBoundTypeArgument(var)) {
		uvar = var;
		lvar = bind(var, SubstsTL[Entity] (Entity v) { return returnSL(replaceWithLower(v)); });
		luvar = bind(uvar, SubstsTL[Entity] (Entity v) { return (entity([ *ids, upper(_) ]) := v) ? returnSL(entity(ids)) : liftTL(tzero()); });
	}
	if(isTypeArgument(var) && !isLowerBoundTypeArgument(var) && !isUpperBoundTypeArgument(var)) {
		lvar = bind(var, SubstsTL[Entity] (Entity v) { return returnSL(entity(v.id + lower(zero()))); }); // rawtypes inference specific
		uvar = bind(var, SubstsTL[Entity] (Entity v) { return returnSL(entity(v.id + upper(zero()))); }); // rawtypes inference specific
		luvar = var;
		if(lvar notin solutions && uvar notin solutions) return "ANY";
	}
	
	str lpp = pp[lvar] ? "";
	str upp = pp[uvar] ? "";
	
	rel[Entity,list[Substs]] lb = run(solutions[lvar]);
	rel[Entity,list[Substs]] ub = run(solutions[uvar]);
	
	rel[Entity,list[Substs]] lbOnes = {<zero(),[]>};
	rel[Entity,list[Substs]] ubOnes = {<zero(),[]>};
	
	list[str] lvarpps = [];
	list[str] uvarpps = [];
		
	if(lpp == "") {		
		if(!isEmpty(lb)) {
			lbOnes = pickTheMostSpecific(facts, mapper, lb);
			for(tuple[Entity,list[Substs]] lbOne<-lbOnes) {
				list[str] lbArgs = [];
				lbArgs = [ prettyprintOneSolution(facts, mapper, returnSL(lookupSubsts(lbOne[1][0], param))) 
								| Entity param <- getTypeParamsOrArgs(lbOne[0]) ];
				lvarpps = lvarpps + ["<prettyprint(lbOne[0])> [<for(arg<-lbArgs){><arg>;<}>]"];
			}
		}
	}
	
	if(upp == "") {
		if(!isEmpty(ub)) {
			ubOnes = pickTheMostSpecific(facts, mapper, ub) - {<entity([ bottom() ]),[]>}; // ensure that the bottom is not an upper bound solution
			for(tuple[Entity,list[Substs]] ubOne<-ubOnes) {
				list[str] ubArgs = [];
				ubArgs = [ prettyprintOneSolution(facts, mapper, returnSL(lookupSubsts(ubOne[1][0], param))) 
								| Entity param <- getTypeParamsOrArgs(ubOne[0]) ];
				uvarpps = uvarpps + ["<prettyprint(ubOne[0])> [<for(arg<-ubArgs){><arg>;<}>]"];
			}
		} 
	}
	
	common = [ *({*lvarpps} & {*uvarpps}) ];
	
	if(isEmpty(lvarpps) && lpp == "") {
		println("<for(<v,_> <-lb){><prettyprint(v)>; <}>");
		throw "Should not ever happen if the initial program is type correct";
	}
		
	if(isEmpty(uvarpps) && upp == "")
		throw "Should not ever happen if the initial program is type correct";
				
	if(!isEmpty(lvarpps) && !isEmpty(uvarpps)) {
		lvarpps = lvarpps - ["Cloneable []"];
		uvarpps = uvarpps - ["Cloneable []"];
		if(!isEmpty(common)) {
			common0 = common - ["Cloneable []"]; // annoying ones, always pops up
			if(!isEmpty(common0))
				common = common0;
			pp[lvar] = common[0];
			pp[uvar] = common[0];
		} else {
			pp[lvar] = lvarpps[0];
			pp[uvar] = uvarpps[0];
		}
	} else if(!isEmpty(lvarpps)) {
		pp[lvar] = lvarpps[0];
	} else if(!isEmpty(uvarpps)){
		pp[uvar] = uvarpps[0];
	}	
	
	if(pp[lvar] == pp[uvar]) {
		pp[luvar] = pp[lvar];
	} else if(pp[lvar] != pp[uvar] && <entity([ bottom() ]),[]> in lb) {
		pp[luvar] = "! extends <pp[uvar]>";
	} else if(pp[lvar] != pp[uvar] && <entity([ bottom() ]),[]> notin lb) {
		pp[luvar] = "! super <pp[lvar]> (<pp[uvar]>)";
	} else {
		pp[luvar] = "! super <pp[lvar]> & extends <pp[uvar]>";	
	}
	
	return pp[var];
	
}

public SubstsTL_[Entity] pickTheMostSpecificLowerBound(CompilUnit facts, Mapper mapper, SubstsTL_[Entity] mvals) {
	rel[Entity,list[Substs]] vals = run(mvals);
	set[Entity] mostSpecificVals = { <Entity val, _> <- pickMostSpecific(facts, mapper, vals) };
	return bind(mvals, SubstsTL_[Entity] (Entity val) {
				return (val in mostSpecificVals) ? returnSL_(val) : liftTL_({}); });
}

public rel[Entity,list[Substs]] pickTheMostSpecific(CompilUnit facts, Mapper mapper, rel[Entity,list[Substs]] vals) {
	bool hadBottom = false;
	if(<entity([ bottom() ]),[]> in vals) {
		hadBottom = true;
		vals = vals - {<entity([ bottom() ]),[]>};
	}
	if(isEmpty(vals)) return {<entity([ bottom() ]),[]>}; // if empty, the bottom has been removed
	rel[Entity,list[Substs]] res = { getOneFrom(vals) };
	solve(res) {
		for(tuple[Entity,list[Substs]] v <- vals) {
			bool found = false;
			for(tuple[Entity,list[Substs]] r <- res, !found) {
				bool sup = !isEmpty(supertype(facts, mapper, <v[0],r[0]>));
				bool sub = !isEmpty(supertype(facts, mapper, <r[0],v[0]>));
				if(sup && !sub) {
					res = res - {r};
					res = res + {v};
					found = true;
				}
				if(!sup && sub) {
					found = true;
				}
			}
			if(!found) {
				res = res + {v};
			}
		}
	}
	if(hadBottom)
		res = res + {<entity([ bottom() ]),[]>};
	return res;
}
