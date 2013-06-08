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

// TODO: also needs to be in a monadic form
public ParamSolutions solutions = ();

// To deal with duplicates
public set[Constraint[SubstsTL[Entity]]] constraints = {};

@doc{EXTENSION with plain generics}
public set[Constraint[SubstsTL[Entity]]] solveit(CompilUnit facts, Mapper mapper, 
												 Constraint::eq(SubstsTL[Entity] lh, SubstsTL[Entity] rh), 
												 bool allConstraints = true) {
												 
	bool lhIsTypeArg = isTypeArgument(lh);
	bool rhIsTypeArg = isTypeArgument(rh);
	
	// left- and right-hand side are both type argument variables	
	if(lhIsTypeArg && rhIsTypeArg) {
		if(lh in solutions) {		
			solutions[lh] = (rh in solutions) ? intersect(facts, mapper, solutions[lh], solutions[rh], 0)
											  : solutions[lh];
			solutions[rh] = (rh in solutions) ? intersect(facts, mapper, solutions[rh], solutions[lh], 0) // Note: reverse order! 
											  : solutions[lh];
		} else if(rh in solutions) { // Note: lh is not in solutions
			solutions[lh] = solutions[rh];
		}
	// only left-hand side is a type argument variable
	} else if(lhIsTypeArg && !rhIsTypeArg) {		
		solutions[lh] = (lh in solutions) ? intersect(facts, mapper, solutions[lh], tauToSubstsTL_(rh), 0) 
										  : tauToSubstsTL_(rh);								
	// only right-hand side is a type argument variable
	} else if(!lhIsTypeArg && rhIsTypeArg) {	
		solutions[rh] = (rh in solutions) ? intersect(facts, mapper, solutions[rh], tauToSubstsTL_(lh), 0) // Note: reverse order! 
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
	
	// left- and right-hand side are both type argument variables	
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
	// only left-hand side is a type argument variable
	} else if(lhIsTypeArg && !rhIsTypeArg) {
		if(lh in solutions || allConstraints)
			solutions[lh] = (lh in solutions) ? intersectLHS(facts, mapper, c, solutions[lh], tauToSubstsTL_(rh))
										  	  : intersectLHS(facts, mapper, c, tauToSubstsTL_(rh));
	// only right-hand side is a type argument variable
	} else if(!lhIsTypeArg && rhIsTypeArg) {
		solutions[rh] = (rh in solutions) ? intersectRHS(facts, mapper, c, tauToSubstsTL_(lh), solutions[rh]) 
								          : intersectRHS(facts, mapper, c, tauToSubstsTL_(lh));								
	}
	
	return { c };
}

public map[tuple[SubstsTL_[Entity],SubstsTL[Entity]],SubstsTL_[Entity]] memoIntersectLHS1 = ();
public map[tuple[SubstsTL_[Entity],SubstsTL_[Entity]],SubstsTL_[Entity]] memoIntersectLHS2 = ();

public SubstsTL_[Entity] intersectLHS(CompilUnit facts, Mapper mapper, Constraint[SubstsTL[Entity]] c, 
																	   SubstsTL_[Entity] r) {
	if(<r,c.lh> in memoIntersectLHS1) return memoIntersectLHS1[<r,c.lh>];
	SubstsT_[Entity] l = bind(tau(tauToSubstsT(c.lh)), SubstsT_[Entity] (Entity var) {
							  return bind(tauToSubstsT_(r), SubstsT_[Entity] (Entity val) {
										return tau(replaceSubsts(facts, mapper, val, var)); }); });
	res = intersect(facts, mapper, tauToSubstsTL_(l), r, -1);
	memoIntersectLHS1[<r,c.lh>] = res;
	return res;
}

public default SubstsTL_[Entity] intersectLHS(CompilUnit facts, Mapper mapper, Constraint[SubstsTL[Entity]] c, 
																	   SubstsTL_[Entity] l, SubstsTL_[Entity] r) {
	if(<l,r> in memoIntersectLHS2) return memoIntersectLHS2[<l,r>];
	SubstsT_[&T] res = bind(tauToSubstsT_(l), SubstsT_[Entity] (Entity lv) { 
							return bind(tau(popSubsts()), SubstsT_[Entity] (Substs substs) {
										SubstsTL_[Entity] cond = intersectRHS(facts, mapper,
																			  c, 
															   				  tauToSubstsTL_(bind(appnd(substs), SubstsT[Entity] (value _) { 
																									return returnS(lv); })),
															   				  r);
										return !isZero(cond) ? returnS_(lv) : lift([]); });
						});				 
	res_ = tauToSubstsTL_(res);
	memoIntersectLHS2[<l,r>] = res_;
	return res_;
}

public map[tuple[SubstsTL_[Entity],SubstsTL[Entity]],SubstsTL_[Entity]] memoIntersectRHS1 = ();
public map[tuple[SubstsTL_[Entity],SubstsTL_[Entity]],SubstsTL_[Entity]] memoIntersectRHS2 = ();

// the case when rhs is an unitialized variable (universe solution)
public SubstsTL_[Entity] intersectRHS(CompilUnit facts, Mapper mapper, Constraint[SubstsTL[Entity]] c, 
																	   SubstsTL_[Entity] l) {
	if(<l,c.rh> in memoIntersectRHS1) return memoIntersectRHS1[<l,c.rh>];															   
	res = intersect(facts, mapper, supertypes_all_(facts, mapper, l, c.rh), supertypes_all_(facts, mapper, l, c.lh), -1);
	memoIntersectRHS1[<l,c.rh>] = res;
	return res;
}

public default SubstsTL_[Entity] intersectRHS(CompilUnit facts, Mapper mapper, Constraint[SubstsTL[Entity]] c, 
																			   SubstsTL_[Entity] l, SubstsTL_[Entity] r) {
	if(<l,r> in memoIntersectRHS2) return memoIntersectRHS2[<l,r>];
	SubstsTL_[Entity] res = intersect(facts, mapper, r, supertypes_all_(facts, mapper, l, returnSL(zero())), -1);
	memoIntersectRHS2[<l,r>] = res;
	return res;
}

public SubstsT[Entity] replaceSubsts(CompilUnit facts, Mapper mapper, Entity val, Entity var) {
	list[Entity] params = getTypeParamsOrArgs(val);
	if(isEmpty(params) || !isTypeArgument(var)) 
		return returnS(val);
	return bind(popSubsts(), SubstsT[Entity] (Substs s) {
							 Substs repl = (  substs([],[]) | concat(it, s_) 
															| Entity param <- params, 
															  Entity arg := lookupSubsts(s, param),
															  arg != zero(),
															  Substs s_ := substs([ entity([ typeArgument(isTypeArgument(arg) ? arg.id[0].name 
																														 	  : param.id[0].name, var, zero()) ]) ], 
														 		 				  [ param ]) );
				return bind(appnd(repl), SubstsT[Entity] (value _) {
							return returnS(val); }); });
}

@doc{Computes ***all*** the supertypes; ***note: it assumes that the input value is a type value in its generic form}
public SubstsT_[Entity] supertypes_all(CompilUnit facts, Mapper mapper, Entity v, Entity var) {
	// New substitution related aspect: introduces new type argument variables, if necessary, before computing supertypes
	SubstsT_[Entity] mv = tau(replaceSubsts(facts, mapper, v, var));
	return bind(mv, SubstsT_[Entity] (Entity v) {
				return bind(isEmpty(getTypeParamsOrArgs(v)) ? discard(returnS_(v)) : returnS_(v), SubstsT_[Entity] (Entity v) {	
							return concat(returnS_(v), 
				   	   					  bind(lift(supertypes(facts, v)), SubstsT_[Entity] (Entity vS) {
				   	   							if(v in getTypeParamsOrArgs(vS)) // takes care of possible cycling dependencies
				   	   								return lift([]);
				   	   							return bind(tau(pushSubsts(paramSubstsWith(facts, mapper, inherits(getGenV(facts, mapper, v), vS)))(facts, mapper, vS)), SubstsT_[Entity] (Entity _) {
															return supertypes_all(facts, mapper, getGenV(facts, mapper, vS), var); }); })); }); });
}
//public SubstsT_[Entity] supertypes_all(CompilUnit facts, Mapper mapper, Entity v) {
//	return bind(isEmpty(getTypeParamsOrArgs(v)) ? discard(returnS_(v)) : returnS_(v), SubstsT_[Entity] (Entity v) {	
//				return concat(returnS_(v), 
//				   	   bind(lift(supertypes(facts, v)), SubstsT_[Entity] (Entity vS) {
//				   	   		if(v in getTypeParamsOrArgs(vS)) // takes care of cycling
//				   	   			return lift([]);
//				   	   		return bind(tau(pushSubsts(paramSubstsWith(facts, mapper, inherits(getGenV(facts, mapper, v), vS)))(facts, mapper, vS)), SubstsT_[Entity] (Entity _) {
//										return supertypes_all(facts, mapper, getGenV(facts, mapper, vS)); }); })); });
//}

@doc{Subtypes semantics; assumes generic type values}
public SubstsT_[Entity] subtypes(CompilUnit facts, Mapper mapper, Entity v) { 
	lrel[Entity,Substs] subs = [ <psub.genval, invert(psup.s)> 
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

@doc{Inverts substitutions and leaves only the ones, which are from type parameter to type parameter}
public Substs invert(Substs s) {
	if(isEmpty(s.params)) return s;
	list[Entity] args = [];
	list[Entity] params = [];
	for(int i <- [0..size(s.params)]) {
		if(isTypeParameter(s.args[i])) {
			args = args + [s.args[i]];
			params = params + [s.params[i]];
		}
	}
	return substs(params, args);
}

public map[tuple[SubstsTL_[Entity],SubstsTL[Entity]],SubstsTL_[Entity]] memoSupertypes = ();

public SubstsTL_[Entity] supertypes_all_(CompilUnit facts, Mapper mapper, SubstsTL_[Entity] mv, SubstsTL[Entity] var) {
	if(<mv,var> in memoSupertypes) return memoSupertypes[<mv,var>];
	SubstsTL_[Entity] res = tauToSubstsTL_(bind(tau(lift(eval(var))), SubstsT_[Entity] (Entity varv) {
												return bind(tauToSubstsT_(mv), SubstsT_[Entity] (Entity v) {
															SubstsT_[Entity] sups = supertypes_all(facts, mapper, v, varv);
															return sups; }); }));
	memoSupertypes[<mv,var>] = res;
	return res;
}
//public SubstsTL_[Entity] supertypes_all_(CompilUnit facts, Mapper mapper, SubstsTL_[Entity] mv) {
//	if(mv in memoSupertypes) return memoSupertypes[mv];
//	SubstsTL_[Entity] res = tauToSubstsTL_(bind(tauToSubstsT_(mv), SubstsT_[Entity] (Entity v) {
//												SubstsT_[Entity] sups = supertypes_all(facts, mapper, v);
//												return sups; }));
//	memoSupertypes[mv] = res;
//	return res;
//}

public map[tuple[SubstsTL_[Entity],SubstsTL_[Entity],int],SubstsTL_[Entity]] memoIntersect = ();

public SubstsTL_[Entity] intersect(CompilUnit facts, Mapper mapper, SubstsTL_[Entity] l, SubstsTL_[Entity] r, int kind) { 
	if(<l,r,kind> in memoIntersect) return memoIntersect[<l,r,kind>];
	SubstsTL_[Entity] res = bind(l, SubstsTL_[Entity] (Entity lv) {
								return bind(r, SubstsTL_[Entity] (Entity rv) { 
											return (lv == rv) ? returnSL_(rv) : liftTL_({}); }); });
	
	res_ = inferMoreTypeArgumentConstraints(facts, mapper, res, kind);
	memoIntersect[<l,r,kind>] = res_;
	return res_;
}

public map[tuple[Entity,list[Substs]],set[Constraint[SubstsT[Entity]]]] memoInference = ();

public SubstsTL_[Entity] inferMoreTypeArgumentConstraints(CompilUnit facts, Mapper mapper, SubstsTL_[Entity] mvals, int kind) {
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
			if(<val,ss0> in memoInference) { 
				inferred = memoInference[<val,ss0>];
			} else {
				inferred = subtyping(facts, mapper, kind == -1 ? Constraint::subtype(lh,rh) : Constraint::eq(lh,rh));
				memoInference[<val,ss0>] = inferred;
			}
			
			// Remove the solution if there is a violated constraint
			if(!isEmpty({ c | Constraint[SubstsT[Entity]] c <- inferred, Constraint::violated(_) := c })) {
				mvals = bind(mvals, SubstsTL_[Entity] (Entity v) { 
							return (v != val_i) ? returnSL_(v) : liftTL_({}); } );
			}
			else constraints = constraints + { tauToSubstsTL(c) | Constraint[SubstsT[Entity]] c <- inferred };
		}
	}
	SubstsTL_[Entity] res = tauToSubstsTL_(tauToSubstsT_(mvals));
	return res; // removes alternative (now under additional constraints) substitutions
}

public bool ifLowerBoundsInferred(CompilUnit facts, Mapper mapper, bool allConstraints = true) {
	set[Constraint[SubstsTL[Entity]]] more =
	{  (!isZero(solutions[mvar]) && !isZero(solutions[upper])) ? c 
															   : { // Undo equality solution - unlikely to happen (TODO: I need to think of it more)
															   	   tracer(true, "WARNING: unlikely undo has happened");
															       constraints = cons; 
															       solutions[mvar] = solutionLower; 
															       if(wasThere) solutions[upper] = solutionUpper; 
															   	   c = Constraint::subtype(mvar, upper); 
															   	   constraints = constraints + {c};
															   	   c; }
			| SubstsTL[Entity] mvar <- solutions,
			  isLowerBoundTypeArgument(mvar), // look up a lower bound type argument variable
			  SubstsTL_[Entity] solutionLower := solutions[mvar], 
			  !isZero(solutionLower),        // the one with non-empty solution
			  SubstsTL[Entity] upper := bind(mvar, SubstsTL[Entity] (Entity v) { 
						   						return returnSL(replaceWithUpper(v)); }), // introduce the upper bound type argument variable
			  Constraint[SubstsTL[Entity]] c := Constraint::subtype(mvar, upper),
			  bool wasThere := (upper in solutions),
			  SubstsTL_[Entity] solutionUpper := solutions[upper] ? liftTL_({}),
			  set[Constraint[SubstsTL[Entity]]] cons := constraints,
			  // try to solve with the equality constraint
			  _ := ( (c notin constraints) ? { constraints = constraints + {c}; solveit(facts, mapper, allConstraints = allConstraints); } 
			  						       : { // DEBUG:
			  							       println("Extra equality constraint is already there.");
			  							       {}; })
			  
	} 
	+ 
	{ c
		| SubstsTL[Entity] mvar <- solutions,
		  isUpperBoundTypeArgument(mvar),
		  SubstsTL[Entity] b := bind(mvar, SubstsTL[Entity] (Entity v) { 
		  						return tauToSubstsTL(bind(boundEnvWithNoCapture(facts, mapper, getTypeParameter(v)), SubstsT[Entity] (Entity bv) {
		  									return (bv == object()) ? lift(tzero()) : returnS(getGenV(facts, mapper, bv)); })); }),
		  !isZero(b),
		  Constraint[SubstsTL[Entity]] c := Constraint::subtype(mvar, b),
		  c notin constraints,
		  _ := { constraints = constraints + {c}; solveit(facts, mapper, allConstraints = allConstraints); {}; }
	};
	
	if(isEmpty(more))
		return false; 

	return true;
}

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

public map[SubstsTL[Entity],str] pp = ();

public void chooseOneSolution(CompilUnit facts, Mapper mapper) {
	println("size of solutions: <size(solutions)>; <size(toRel(solutions))>");
	for(SubstsTL[Entity] var <- solutions) {
		prettyprintOneSolution(facts, mapper, var);
	}
	
	tracer(true, "One solution: \n <for(var<-pp){><prettyprint(var)> = <pp[var]>\n<}>");
	tracer(true, "More relevant part of the solution: \n <for(var<-pp,!isLowerBoundTypeArgument(var)&&!isUpperBoundTypeArgument(var)){><prettyprint(var)> = <pp[var]>\n<}>");
}

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
			ubOnes = pickTheMostSpecific(facts, mapper, ub);
			for(tuple[Entity,list[Substs]] ubOne<-ubOnes) {
				list[str] ubArgs = [];
				ubArgs = [ prettyprintOneSolution(facts, mapper, returnSL(lookupSubsts(ubOne[1][0], param))) 
								| Entity param <- getTypeParamsOrArgs(ubOne[0]) ];
				uvarpps = uvarpps + ["<prettyprint(ubOne[0])> [<for(arg<-ubArgs){><arg>;<}>]"];
			}
		} 
	}
	
	common = [ *({*lvarpps} & {*uvarpps}) ];
	
	if(isEmpty(lvarpps) && lpp == "")
		pp[lvar] = "_; []";
		
	if(isEmpty(uvarpps) && upp == "")
		pp[uvar] = "_; []";
				
	if(!isEmpty(lvarpps) && !isEmpty(uvarpps)) {
		if(!isEmpty(common)) {
			common0 = common - ["Serializable; []", "Cloneable; []"]; // annoying ones, always pops up
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
	
	if(pp[lvar] == pp[uvar] && pp[lvar] != "_; []") {
		pp[luvar] =  pp[lvar];
	} else if(pp[lvar] != pp[uvar] && pp[lvar] == "_; []") {
		pp[luvar] = "! extends <pp[uvar]>";
	} else if(pp[lvar] != "_; []" && <object(),[]> in ub) {
		pp[luvar] =  "! super <pp[lvar]>";
	} else {
		pp[luvar] = "! super <pp[lvar]> & extends <pp[uvar]>";	
	}
	
	return pp[var];
	
}

public rel[Entity,list[Substs]] pickTheMostSpecific(CompilUnit facts, Mapper mapper, rel[Entity,list[Substs]] vals) {
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
	return res;
}
