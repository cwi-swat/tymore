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
import prototype::computations::mksubsts::BoundSemWithoutWildCards;
import prototype::computations::mksubsts::BoundSemWithWildCards;
import prototype::computations::mksubsts::LanguageInterface;
import prototype::computations::mksubsts::Monads;
import prototype::computations::mksubsts::TypeComputation;
import prototype::computations::mksubsts::FunctionsOfTypeValues;

import IO;
import List;
import Map;
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
			solutions[lv] = (rv in solutions) ? intersect(facts, mapper, solutions[lv], solutions[rv], 0)
											  : solutions[lv];
			solutions[rv] = (rv in solutions) ? intersect(facts, mapper, solutions[rv], solutions[lv], 0) // Note: reverse order! 
											  : solutions[lv];
		} else if(rv in solutions) { // Note: lv is not in solutions
			solutions[lv] = solutions[rv];
		}
	// only left-hand side is a type argument variable
	} else if(lhIsTypeArg && !rhIsTypeArg) {		
		solutions[lv] = (lv in solutions) ? intersect(facts, mapper, solutions[lv], tauToSubstsTL_(rh), 0) 
										  : tauToSubstsTL_(rh);								
	// only right-hand side is a type argument variable
	} else if(!lhIsTypeArg && rhIsTypeArg) {	
		solutions[rv] = (rv in solutions) ? intersect(facts, mapper, solutions[rv], tauToSubstsTL_(lh), 0) // Note: reverse order! 
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
											  : { sups = supertypes_all_(facts, mapper, replaceSubsts(mapper, solutions[lv], rh)); // solutions[lv];
												  intersectRHS(facts, mapper, solutions[lv], replaceSubsts(mapper, sups, rh)); };
		} else if(rv in solutions) { // Note: lv is not in solutions
			solutions[lv] = intersectLHS(facts, mapper, replaceSubsts(mapper, solutions[rv], lh), solutions[rv]); // TODO: should be actually subtypes
		}
	// only left-hand side is a type argument variable
	} else if(lhIsTypeArg && !rhIsTypeArg) {
		solutions[lv] = intersectLHS(facts, mapper, (lv in solutions) ? solutions[lv] : replaceSubsts(mapper, tauToSubstsTL_(rh), lh), // TODO: should be actually subtypes 
													tauToSubstsTL_(rh));
	// only right-hand side is a type argument variable
	} else if(!lhIsTypeArg && rhIsTypeArg) {
		solutions[rv] = (rv in solutions) ? intersectRHS(facts, mapper, tauToSubstsTL_(lh), solutions[rv]) 
								: { sups = supertypes_all_(facts, mapper, replaceSubsts(mapper, tauToSubstsTL_(lh), rh)); // tauToSubstsTL_(lh)
									intersectRHS(facts, mapper, tauToSubstsTL_(lh), replaceSubsts(mapper, sups, rh)); };								
	}
	
	return { Constraint::subtype(lh, rh) };
}

public SubstsTL_[Entity] replaceSubsts(Mapper mapper, SubstsTL_[Entity] vals, SubstsTL[Entity] var) {
	return tauToSubstsTL_(bind(tau(lift(eval(var))), SubstsT_[Entity] (Entity varv) {
								return bind(tauToSubstsT_(vals), SubstsT_[Entity] (Entity val) {
											list[Entity] params = getTypeParamsOrArgs(val);
											if(isEmpty(params)) return returnS_(val);
											return bind(lift(params), SubstsT_[Entity] (Entity param) {
														return bind(tau(boundS_(mapper, param)), SubstsT_[Entity] (Entity v) {
																	return bind(tau(appnd(substs([ entity([ typeArgument(isTypeArgument(v) ? v.id[0].name : param.id[0].name, varv, zero()) ]) ], 
																		   		   		   		 [ param ]))), SubstsT_[Entity] (value _) {
																				return returnS_(val); }); }); }); }); }));
}

public map[SubstsTL_[Entity],SubstsTL_[Entity]] memoSupertypes = ();

public SubstsTL_[Entity] supertypes_all_(CompilUnit facts, Mapper mapper, SubstsTL_[Entity] mv) {
	if(mv in memoSupertypes) return memoSupertypes[mv];
	SubstsTL_[Entity] res = tauToSubstsTL_(bind(tauToSubstsT_(mv), SubstsT_[Entity] (Entity v) {
												return supertypes_all(facts, mapper, v); }));
	memoSupertypes[mv] = res;
	return res;
}

public map[tuple[SubstsTL_[Entity],SubstsTL_[Entity]],SubstsTL_[Entity]] memoIntersectLHS = ();

public SubstsTL_[Entity] intersectLHS(CompilUnit facts, Mapper mapper, SubstsTL_[Entity] l, SubstsTL_[Entity] r) {
	if(<l,r> in memoIntersectLHS) return memoIntersectLHS[<l,r>];
	SubstsT_[&T] l_ = tauToSubstsT_(l);
	SubstsT_[&T] res = bind(l_, SubstsT_[Entity] (Entity lv) { 
							return bind(tau(popSubsts()), SubstsT_[Entity] (Substs substs) {
										SubstsTL_[Entity] cond = intersectRHS(facts, mapper, 
															   				  tauToSubstsTL_(bind(appnd(substs), SubstsT[Entity] (value _) { 
																									return returnS(lv); })),
															   				  r);				 
										return !isZero(cond) ? returnS_(lv) : lift([]); });
						});
	res_ = tauToSubstsTL_(res);
	memoIntersectLHS[<l,r>] = res_;
	return res_;
}

public map[tuple[SubstsTL_[Entity],SubstsTL_[Entity]],SubstsTL_[Entity]] memoIntersectRHS = ();

public SubstsTL_[Entity] intersectRHS(CompilUnit facts, Mapper mapper, SubstsTL_[Entity] l, SubstsTL_[Entity] r) {
	if(<l,r> in memoIntersectRHS) return memoIntersectRHS[<l,r>];
	SubstsTL_[Entity] res = intersect(facts, mapper, r, supertypes_all_(facts, mapper, l), -1);
	memoIntersectRHS[<l,r>] = res;
	return res;
}

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

public bool ifLowerBoundsInferred(CompilUnit facts, Mapper mapper) {
	set[Constraint[SubstsTL[Entity]]] more =
	{  (!isZero(solutions[mvar]) && !isZero(solutions[upper])) ? c 
															   : { // Undo equality solution - unlikely to happen (TODO: I need to think of it more)
															   	   tracer(true, "WARNING: unlikely undo has happened");
															       constraints = cons; solutions[mvar] = solutionLower; if(wasThere) solutions[upper] = solutionUpper; 
															   	   Constraint[SubstsTL[Entity]] c_ = Constraint::subtype(tauToSubstsTL(lift(mvar)), tauToSubstsTL(lift(upper))); 
															   	   constraints = constraints + c_;
															   	   c_; }
			| TypeOf[Entity] mvar <- solutions,
			  Entity var <- eval(tau(lift(mvar))), 
			  isLowerBoundTypeArgument(var), // look up a lower bound type argument variable
			  SubstsTL_[Entity] solutionLower := solutions[mvar], 
			  !isZero(solutionLower),      // the one with non-empty solution
			  TypeOf[Entity] upper := bind(mvar, TypeOf[Entity] (Entity v) { 
						   					return returnT(replaceWithUpper(v)); }), // introduce the upper bound type argument variable
			  Constraint[SubstsTL[Entity]] c := Constraint::eq(tauToSubstsTL(lift(mvar)), tauToSubstsTL(lift(upper))),
			  bool wasThere := (upper in solutions),
			  SubstsTL_[Entity] solutionUpper := solutions[upper] ? liftTL_({}),
			  set[Constraint[SubstsTL[Entity]]] cons := constraints,
			  _ := { constraints = constraints + c; solveit(facts, mapper); } // try to solve with the equality constraint
			  
	};
	if(isEmpty(more))
		return false; 
	
	//tracer(true, "<for(con<-more){><prettyprint(con)>\n<}>");
	//tracer(true, "<for(s<-solutions){><prettyprint(s)> == <prettyprint(solutions[s])>\n<}>");
	
	// constraints = constraints + more;
	return true;
}

public bool solveit(CompilUnit facts, Mapper mapper) {
	int n = size(constraints);
	solve(solutions, n) {
		println("solve <size(constraints)> ...");
		set[Constraint[SubstsTL[Entity]]] constrs = constraints;
		{ *solveit(facts, mapper, c) | Constraint[SubstsTL[Entity]] c <- constrs };
		n = size(constraints);
	}
	return true;
}

public map[TypeOf[Entity],str] pp = ();

public void chooseOneSolution(CompilUnit facts, Mapper mapper) {
	for(TypeOf[Entity] var <- solutions) {
		prettyprintOneSolution(facts, mapper, var);
	}
	
	tracer(true, "One solution: \n <for(var<-pp){><prettyprint(var)> = <pp[var]>\n<}>");
	tracer(true, "More relevant part of the solution: \n <for(var<-pp,!isLowerBoundTypeArgument(var.v)&&!isUpperBoundTypeArgument(var.v)){><prettyprint(var)> = <pp[var]>\n<}>");
}

public str prettyprintOneSolution(CompilUnit facts, Mapper mapper, TypeOf[Entity] var) {
	if(!isTypeArgument(var.v)) 
		return "<prettyprint(var)>";
	
	TypeOf[Entity] lvar = tzero();
	TypeOf[Entity] uvar = tzero();
	TypeOf[Entity] luvar = tzero();
		
	if(isLowerBoundTypeArgument(var.v)) {
		lvar = var;
		uvar = bind(var, TypeOf[Entity] (Entity v) { return returnT(replaceWithUpper(v)); });
		luvar = bind(lvar, TypeOf[Entity] (Entity v) { return (entity([ *ids, lower(_) ]) := v) ? returnT(entity(ids)) : tzero(); });
	}	
	if(isUpperBoundTypeArgument(var.v)) {
		uvar = var;
		lvar = bind(var, TypeOf[Entity] (Entity v) { return returnT(replaceWithLower(v)); });
		luvar = bind(uvar, TypeOf[Entity] (Entity v) { return (entity([ *ids, upper(_) ]) := v) ? returnT(entity(ids)) : tzero(); });
	}
	if(isTypeArgument(var.v) && !isLowerBoundTypeArgument(var.v) && !isUpperBoundTypeArgument(var.v)) {
		lvar = bind(var, TypeOf[Entity] (Entity v) { return returnT(entity(v.id + lower(zero()))); }); // rawtypes inference specific
		uvar = bind(var, TypeOf[Entity] (Entity v) { return returnT(entity(v.id + upper(zero()))); }); // rawtypes inference specific
		luvar = var;
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
				lbArgs = [ prettyprintOneSolution(facts, mapper, returnT(lookupSubsts(lbOne[1][0], param))) 
								| Entity param <- getTypeParamsOrArgs(lbOne[0]) ];
				lvarpps = lvarpps + ["<prettyprint(lbOne[0])>; [<for(arg<-lbArgs){><arg>;<}>]"];
			}
		}
	}
	
	if(upp == "") {
		if(!isEmpty(ub)) {
			ubOnes = pickTheMostSpecific(facts, mapper, ub);
			for(tuple[Entity,list[Substs]] ubOne<-ubOnes) {
				list[str] ubArgs = [];
				ubArgs = [ prettyprintOneSolution(facts, mapper, returnT(lookupSubsts(ubOne[1][0], param))) 
								| Entity param <- getTypeParamsOrArgs(ubOne[0]) ];
				uvarpps = uvarpps + ["<prettyprint(ubOne[0])>; [<for(arg<-ubArgs){><arg>;<}>]"];
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
