@license{
  Copyright (c) 2009-2011 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - A.Izmaylova@cwi.nl}
module prototype::computations::mksubsts::ConstraintInference

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import prototype::lang::java::jdt::refactorings::Java;
import prototype::lang::java::jdt::refactorings::JavaADT;
import prototype::lang::java::jdt::refactorings::JavaADTVisitor;
import prototype::lang::java::jdt::refactorings::PrettyPrintUtil;
import prototype::lang::java::jdt::refactorings::ValuesUtil;

import prototype::computations::mksubsts::ConstraintComputation;
import prototype::computations::mksubsts::BoundSemWithoutWildCards0;
import prototype::computations::mksubsts::BoundSemWithWildCards0;
import prototype::computations::mksubsts::LanguageInterface;
import prototype::computations::mksubsts::Monads;
import prototype::computations::mksubsts::TypeComputation;
import prototype::computations::mksubsts::FunctionsOfTypeValues;

import List;
import Map;
import Set;
import IO;

//@doc{Evaluates the left and right hand side of a constraint;
//	 Note: semantically, left- and right-hand side may be of the forms:
//	 		(a) C (non-generic type); (b) C<...Ai...> (generic type); (c) A (type parameter); 
//}
//public set[Constraint[SubstsT[Entity]]] gevalc(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
//	= { apply(SubstsT[Entity] (Entity v) { 
//				return bind(gevalc(facts, mapper, v), SubstsT[Entity] (Entity v_) {
//								return returnS(eval(getGenV(facts, mapper, v))); }); })(c) }; 

@doc{Binds type parameters ignoring the case of a type argument variable,
	 i.e. stops when bound to a type argument variable}
public set[Constraint[SubstsT[Entity]]] bindS_(CompilUnit facts, Mapper mapper, c:violated(_)) = { c };
public default set[Constraint[SubstsT[Entity]]] bindS_(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(bindS_(facts, mapper, v), SubstsT[Entity] (Entity b) {
							// ***Note: type value is a generic type value 
							Entity gen = getGenV(facts, mapper, b);
							return (isEmpty(getTypeParamsOrArgs(gen)) 
									/*&& !isTypeArgument(gen)*/) ? discard(returnS(gen)) : returnS(gen); }); })(c) }; 

@doc{Binds type parameters and type argument variables}
public set[Constraint[SubstsT[Entity]]] bindS(CompilUnit facts, Mapper mapper, c:violated(_)) = { c };
public default set[Constraint[SubstsT[Entity]]] bindS(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(bindS(facts, mapper, v), SubstsT[Entity] (Entity b) {
							// ***Note: type value is a generic type value
							Entity gen = getGenV(facts, mapper, b);
							return isEmpty(getTypeParamsOrArgs(gen)) ? discard(returnS(gen)) : returnS(gen); }); })(c) };

@doc{Computes the supertype predicate of the left-hand side given the right-hand side}
public set[Constraint[SubstsT[Entity]]] supertypec(CompilUnit facts, Mapper mapper, c:violated(_)) = { c };		
public set[Constraint[SubstsT[Entity]]] supertypec(CompilUnit facts, Mapper mapper, Constraint::eq(SubstsT[Entity] lh, SubstsT[Entity] rh)) {
	lh = runWithEmptySubsts(lh);
	rh = runWithEmptySubsts(rh);
	
	lh_ = bind(rh, SubstsT[Entity] (Entity rv) { 
				return bind(lh, SubstsT[Entity] (Entity lv) {
							return lv == rv ? returnS(lv) : lift(tzero()); }); });
	
	// ***Note: violation of a constraint results in a zero computation
	return ( nonZero := catchZ(Constraint::eq(lh_,rh)) && !isEmpty(nonZero) ) ? nonZero : { Constraint::violated("Equality constraint does not hold!") } ;
}	
public set[Constraint[SubstsT[Entity]]] supertypec(CompilUnit facts, Mapper mapper, Constraint::subtype(SubstsT[Entity] lh, SubstsT[Entity] rh)) {
	lh = runWithEmptySubsts(lh);
	rh = runWithEmptySubsts(rh);
	
	if(isBottom(lh)) return {};
	
	lh_ = bind(rh, SubstsT[Entity] (Entity rv) { 
			return bind(lh, SubstsT[Entity] (Entity lv) {
						SubstsT[bool] isSup = tauInv(supertypec_(facts, mapper, <lv, rv>)); 
						return bind(isSup, SubstsT[Entity] (bool b) { 
									return returnS(rv); }); }); });
	
	// ***Note: violation of a constraint results in a zero computation
	return ( nonZero := catchZ(Constraint::subtype(lh_,rh)) && !isEmpty(nonZero) ) ? nonZero : { Constraint::violated("Subtype constraint does not hold!") };
}

//@doc{Infers additional type constraints from subtype constraints}
//public set[Constraint[SubstsT[Entity]]] inferTypeArguments(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
//	cons = { c2 | Constraint[SubstsT[Entity]] c1  <- gevalc(facts, mapper, c),
//			      Constraint[SubstsT[Entity]] c2  <- bindS_(facts, mapper, c1) 
//		   };
//		   
//	return { c2 | Constraint[SubstsT[Entity]] c1 <- cons,
//				  // adds only constraints that have type argument variables
//				  Constraint[SubstsT[Entity]] c2 <- catchTypeArgVariable(c1)
//		   } 
//		   + 
//		   { c3 | Constraint[SubstsT[Entity]] c1  <- cons,
//		   
//				  Constraint[SubstsT[Entity]] c2  <- bindS(facts, mapper, c1),
//				  Constraint[SubstsT[Entity]] c2_ <- catchZ(c2), // zero may occur due to raw types
//				  
//				  Constraint[SubstsT[Entity]] c3  <- subtyping(facts, mapper, c2_)
//	  	   };
//}

@doc{***Recursive subtyping with regard to type arguments}
public set[Constraint[SubstsT[Entity]]] subtyping(CompilUnit facts, Mapper mapper, c:violated(_)) = { c };
public default set[Constraint[SubstsT[Entity]]] subtyping(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	set[Constraint[SubstsT[Entity]]] constraints = 
			{ runWithEmptySubsts(c3)
				 | Constraint[SubstsT[Entity]] c1  <- bindS(facts, mapper, c), 
				   Constraint[SubstsT[Entity]] c1_ <- catchZ(c1), // zero may occur, for example, due to raw types		
				      
				   Constraint[SubstsT[Entity]] c2  <- supertypec(facts, mapper, c1_), 	  
				   Constraint[SubstsT[Entity]] c3  <- invariant(facts, mapper, c2)
			};
			
	return { c2 | Constraint[SubstsT[Entity]] c1 <- constraints,
				  // adds only constraints that have type argument variables 
				  Constraint[SubstsT[Entity]] c2  <- catchTypeArgVariable(c1) 
		   }
		   +
		   { c2 | Constraint[SubstsT[Entity]] c1 <- constraints,  
		   		  // recur also on unconstrained type arguments to perform the check of subtyping wrt type arguments
				  Constraint[SubstsT[Entity]] c2 <- subtyping(facts, mapper, c1)
		   }
		   ;
}

//@doc{Invariant function that imposes equality constraints on type arguments}
//public set[Constraint[SubstsT[Entity]]] invariant(CompilUnit facts, Mapper mapper, c:violated(_)) = { c };
//public default set[Constraint[SubstsT[Entity]]] invariant(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
//	return { c2_ | Entity rv    <- eval(tau(c.rh)),
//				   Entity param <- getTypeParamsOrArgs(getGenV(facts, mapper, rv)), 
//				   Constraint[SubstsT[Entity]] c1  := { p = param; apply(SubstsT[Entity] (Entity _) { return returnS(p); })(c); }, // Attension: current rascal closure semantics
//				   Constraint[SubstsT[Entity]] c1_ := eq(c1.lh, c1.rh), // turns into an equality constraint and adds it
//				   Constraint[SubstsT[Entity]] c2  <- bindS_(facts, mapper, c1_),
//				   Constraint[SubstsT[Entity]] c2_ <- catchZ(c2)
//		   };
//}

public set[Constraint[SubstsT[Entity]]] catchTypeArgVariable(c:violated(_)) = { c };
public default set[Constraint[SubstsT[Entity]]] catchTypeArgVariable(Constraint[SubstsT[Entity]] c) {
	Constraint[SubstsT[Entity]] c_ = runWithEmptySubsts(c);
	
	if(isBottom(c_.lh)) return {};
	
	bool lhIsTypeArg = isTypeArgument(c_.lh);
	bool rhIsTypeArg = isTypeArgument(c_.rh);
	// Filters out constraints with the same type argument variable on both sides
	if(lhIsTypeArg && rhIsTypeArg && eval(c_.lh) == eval(c_.rh)) return {};
	if(lhIsTypeArg || rhIsTypeArg) {
		SubstsT[Entity] (Entity) f = SubstsT[Entity] (Entity v) { 
										return isTypeArgument(v) ? discard(returnS(v)) : returnS(v) ; };
		return { apply(f)(c_) };
	}
	return {};
}

public bool isTypeArgument(TypeOf[Entity] v)
	= !isZero(bind(v, TypeOf[Entity] (Entity v_) { 
					return isTypeArgument(v_) ? returnT(v_) : tzero(); }));
public bool isTypeArgument(SubstsT[Entity] v) = isTypeArgument(eval(v));
public bool isTypeArgument(SubstsTL[Entity] v) = isTypeArgument(tauToSubstsT(v));

//public set[Constraint[SubstsT[Entity]]] bindTypeArgumentIfNotRawType(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c:violated(_)) = { c };
//public default set[Constraint[SubstsT[Entity]]] bindTypeArgumentIfNotRawType(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
//	SubstsT[Entity] (Entity) f = SubstsT[Entity] (Entity v) {
//									if(isTypeArgument(v)) {
//										SubstsT[Entity] b = bind(bindS(facts, mapper, v), SubstsT[Entity] (Entity bnd) { 
//																// DEBUG: println("Bind type argument variables if not a raw type: <prettyprint(v)> <prettyprint(bnd)>"); 
//																return returnS(getGenV(facts, mapper, bnd)); });
//										// ***Note: rawtypes specific optimization, should not be earlier
//										return catchZ(b, discard(returnS(v))); // discard(returnS(v));
//									}
//									return returnS(v);  };
//	return { apply(f)(c) };
//}

@doc{EXTENSION with wildcards: overrides the left hand side evaluation to account for wildcards}
public default set[Constraint[SubstsT[Entity]]] gevalc(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(gevalc(facts, mapper, v), SubstsT[Entity] (Entity v_) {
								return returnS(eval(getGenV(facts, mapper, v))); }); },
			  SubstsT[Entity] (Entity v) { 
				return bind(gevalcNoCapture(facts, mapper, v), SubstsT[Entity] (Entity v_) {
								return returnS(eval(getGenV(facts, mapper, v))); }); })(c) }; 

@doc{EXTENSION with wildcards: extends the bind semantics to account for wildcards and splits it into the lower and upper bind semantics }
public set[Constraint[SubstsT[Entity]]] bindSu_(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(bindSu_(facts, mapper, v), SubstsT[Entity] (Entity b) {
							// ***Note: type value is a generic type value
							Entity gen = getGenV(facts, mapper, b);
							return isEmpty(getTypeParamsOrArgs(gen)) ? discard(returnS(gen)) : returnS(gen); }); })(c) }; 
public set[Constraint[SubstsT[Entity]]] bindSu(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(bindSu(facts, mapper, v), SubstsT[Entity] (Entity b) {
							// ***Note: type value is a generic type value
							Entity gen = getGenV(facts, mapper, b);
							return isEmpty(getTypeParamsOrArgs(gen)) ? discard(returnS(gen)) : returnS(gen); }); })(c) };
public set[Constraint[SubstsT[Entity]]] bindSl_(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(bindSl_(facts, mapper, v), SubstsT[Entity] (Entity b) {
							// ***Note: type value is a generic type value
							Entity gen = getGenV(facts, mapper, b);
							return isEmpty(getTypeParamsOrArgs(gen)) ? discard(returnS(gen)) : returnS(gen); }); })(c) };
public set[Constraint[SubstsT[Entity]]] bindSl(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(bindSl(facts, mapper, v), SubstsT[Entity] (Entity b) {
							// ***Note: type value is a generic type value
							Entity gen = getGenV(facts, mapper, b);
							return isEmpty(getTypeParamsOrArgs(gen)) ? discard(returnS(gen)) : returnS(gen); }); })(c) };
// Explicit one level capturing
public set[Constraint[SubstsT[Entity]]] boundSul_(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { c2 | Constraint[SubstsT[Entity]] c1 := apply(SubstsT[Entity] (Entity v) { 
														return bind(bindS_(facts, mapper, v), SubstsT[Entity] (Entity b) {
																	// ***Note: type value is a generic type value
																	Entity gen = getGenV(facts, mapper, b);
																	return isEmpty(getTypeParamsOrArgs(gen)) ? discard(returnS(gen)) : returnS(gen); }); })(c),
			Constraint[SubstsT[Entity]] c2 <- capture(facts, mapper, c1) 
	  };
// Explicit one level capturing
public set[Constraint[SubstsT[Entity]]] boundSul(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { c1 | Constraint[SubstsT[Entity]] c1 := apply(SubstsT[Entity] (Entity v) { 
														return bind(bindSu(facts, mapper, v), SubstsT[Entity] (Entity b) {
																	// ***Note: type value is a generic type value
																	Entity gen = getGenV(facts, mapper, b);
																	return isEmpty(getTypeParamsOrArgs(gen)) ? discard(returnS(gen)) : returnS(gen); }); },
			  										 SubstsT[Entity] (Entity v) { 
														return bind(bindSl(facts, mapper, v), SubstsT[Entity] (Entity b) {
																	// ***Note: type value is a generic type value
																	Entity gen = getGenV(facts, mapper, b);
																	return isEmpty(getTypeParamsOrArgs(gen)) ? discard(returnS(gen)) : returnS(gen); }); })(c) 
	  };    

public set[Constraint[SubstsT[Entity]]] capture(CompilUnit facts, Mapper mapper, Constraint::supertype(SubstsT[Entity] lh, SubstsT[Entity] rh)) {
	Constraint[SubstsT[Entity]] c_ = runWithEmptySubsts(Constraint::supertype(lh,rh));
	bool lhIsCapturedTypeArg = isCapturedTypeArgument(c_.lh);
	SubstsT[Entity] (Entity) fu = SubstsT[Entity] (Entity v) { 
												return bind(bindSu_(facts, mapper, v), SubstsT[Entity] (Entity b) {
															Entity gen = getGenV(facts, mapper, b);
															return isEmpty(getTypeParamsOrArgs(gen)) ? discard(returnS(gen)) : returnS(gen); }); };
	SubstsT[Entity] (Entity) fl = SubstsT[Entity] (Entity v) { 
												return bind(bindSl_(facts, mapper, v), SubstsT[Entity] (Entity b) {
															Entity gen = getGenV(facts, mapper, b);
															return isEmpty(getTypeParamsOrArgs(gen)) ? discard(returnS(gen)) : returnS(gen); }); };
	Constraint[SubstsT[Entity]] cul = apply(fu,fl)(c_);
	if(!lhIsCapturedTypeArg)
		return { Constraint::subtype(cul.rh,cul.lh) };
	println("Special case: <prettyprint(lh)> \>: <prettyprint(rh)>");
	// Special case:
	cc = apply(SubstsT[Entity] (Entity v) { return capture(facts, mapper, v); },
		  	   SubstsT[Entity] (Entity v) { return returnS(v); })(cul); // captured(Ta_ub)
	// Extra constraint if captured type argument variable
	return { Constraint::subtype(cc.rh,cc.lh), 
			 apply(fl,fu)(Constraint::eq(c_.lh,c_.lh)),
			 Constraint::eq(cc.lh, bind(cc.lh, SubstsT[Entity] (Entity lh) { 
											  return uncapture(facts, mapper, lh); })) };

}
public default set[Constraint[SubstsT[Entity]]] capture(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	Constraint[SubstsT[Entity]] c_ = runWithEmptySubsts(c);
	bool lhIsCapturedTypeArg = isCapturedTypeArgument(c_.lh);
	SubstsT[Entity] (Entity) fu = SubstsT[Entity] (Entity v) { 
												return bind(bindSu_(facts, mapper, v), SubstsT[Entity] (Entity b) {
															Entity gen = getGenV(facts, mapper, b);
															return isEmpty(getTypeParamsOrArgs(gen)) ? discard(returnS(gen)) : returnS(gen); }); };
	SubstsT[Entity] (Entity) fl = SubstsT[Entity] (Entity v) { 
												return bind(bindSl_(facts, mapper, v), SubstsT[Entity] (Entity b) {
															Entity gen = getGenV(facts, mapper, b);
															return isEmpty(getTypeParamsOrArgs(gen)) ? discard(returnS(gen)) : returnS(gen); }); };
	Constraint[SubstsT[Entity]] cul = apply(fu,fl)(c_);
	if(!lhIsCapturedTypeArg)
		return { cul };
	cc = apply(SubstsT[Entity] (Entity v) { return capture(facts, mapper, v); },
		  	   SubstsT[Entity] (Entity v) { return returnS(v); })(cul);
	return { cc, 
			 cul,
			 Constraint::subtype(cc.lh, bind(cc.lh, SubstsT[Entity] (Entity lh) { 
											  return uncapture(facts, mapper, lh); })) };
}

@doc{EXTENSION with wildcards: the inference function needs to use a different (lower and upper) bind semantics}
public set[Constraint[SubstsT[Entity]]] inferTypeArguments(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	cons = { runWithEmptySubsts(c2) 
				| Constraint[SubstsT[Entity]] c1 <- gevalc(facts, mapper, c),
			      Constraint[SubstsT[Entity]] c2 <- boundSul_(facts, mapper, c1)//, // ***Note: no capture values expected, but captured type argument variables
		    };
		   
	return { c2 | Constraint[SubstsT[Entity]] c1 <- cons,
				  // adds only constraints that have type argument variables
				  Constraint[SubstsT[Entity]] c2 <- catchTypeArgVariable(c1)
		   } 
		   + 
		   { c3 | Constraint[SubstsT[Entity]] c1  <- cons,	   
				  Constraint[SubstsT[Entity]] c2  <- boundSul(facts, mapper, c1), // ***Note: removes captured types
				  Constraint[SubstsT[Entity]] c2_ <- catchZ(c2), // zero may occur due to raw types
				  Constraint[SubstsT[Entity]] c3  <- subtyping(facts, mapper, c2_)
	  	   };
}

@doc{EXTENSION with wildcards: extends the invariant function to also impose covariance and contravariance}
public set[Constraint[SubstsT[Entity]]] invariant(CompilUnit facts, Mapper mapper, c:violated(_)) = { c };
public set[Constraint[SubstsT[Entity]]] invariant(CompilUnit facts, Mapper mapper, Constraint::eq(SubstsT[Entity] lh, SubstsT[Entity] rh)) {
	return { c2_ | Entity rv    <- eval(tau(rh)),
			   	   Entity param <- getTypeParamsOrArgs(getGenV(facts, mapper, rv)), 
			  
			       Constraint[SubstsT[Entity]] c1 := { p = param; apply(SubstsT[Entity] (Entity _) { return returnS(p); })(Constraint::eq(lh,rh)); }, // Attension: current rascal closure semantics
			       Constraint[SubstsT[Entity]] c2  <- bindSu_(facts, mapper, c1) 
			       									  + bindSl_(facts, mapper, c1),
			       Constraint[SubstsT[Entity]] c2_ <- catchZ(c2)
	   };
}
public default set[Constraint[SubstsT[Entity]]] invariant(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	return { c3_ | Entity rv    <- eval(tau(c.rh)),
				   Entity param <- getTypeParamsOrArgs(getGenV(facts, mapper, rv)), 
				  
				   Constraint[SubstsT[Entity]] c1 := { p = param; apply(SubstsT[Entity] (Entity _) { return returnS(p); })(c); }, // Attension: current rascal closure semantics
				   Constraint[SubstsT[Entity]] c2  <- bindS_(facts, mapper, eq(c1.lh, c1.rh)), // ***Note: capture values could occur here
				   Constraint[SubstsT[Entity]] c2_ <- catchZ(c2),
				  
				   // leaves equality constraints (invariance) only in case of captures, otherwise drops it
				   Constraint[SubstsT[Entity]] c3  <- catchCaptureVariable(facts, mapper, c2_),
				   Constraint[SubstsT[Entity]] c3_ <- catchZ(c3)
		   } 
		   + covariant(facts, mapper, c) 
		   + contravariant(facts, mapper, c);
}

@doc{EXTENSION with wildcards: adds constraints to account for covariance}
public set[Constraint[SubstsT[Entity]]] covariant(CompilUnit facts, Mapper mapper, c:violated(_)) = { c };
public default set[Constraint[SubstsT[Entity]]] covariant(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	return { c4 | Entity rv    <- eval(tau(c.rh)), 
				  Entity param <- getTypeParamsOrArgs(getGenV(facts, mapper, rv)),
				  Constraint[SubstsT[Entity]] c1 := { p = param; apply(SubstsT[Entity] (Entity _) { return returnS(p); })(c); }, // Attension: current rascal closure semantics
				  Constraint[SubstsT[Entity]] c2 <- bindS_(facts, mapper, c1),
				  Constraint[SubstsT[Entity]] c2_ <- catchZ(c2),
				  
				  // adds a subtype constraint on upper bounds
				  Constraint[SubstsT[Entity]] c3 <- { isCapturedTypeArgument(c2_.rh) ? {} : { c2_ }; },
				  Constraint[SubstsT[Entity]] c4 <- bindSu_(facts, mapper, subtype(c3.lh,c3.rh))
		   };
}

@doc{EXTENSION with wildcards: adds constraints to account for contravariance}
public set[Constraint[SubstsT[Entity]]] contravariant(CompilUnit facts, Mapper mapper, c:violated(_)) = { c };
public default set[Constraint[SubstsT[Entity]]] contravariant(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	return { c4 | Entity rv    <- eval(tau(c.rh)),
				  Entity param <- getTypeParamsOrArgs(getGenV(facts, mapper, rv)), 	  
				  Constraint[SubstsT[Entity]] c1 := { p = param; apply(SubstsT[Entity] (Entity _) { return returnS(p); })(c); }, // Attension: current rascal closure semantics
				  Constraint[SubstsT[Entity]] c2 <- bindS_(facts, mapper, c1),
				  Constraint[SubstsT[Entity]] c2_ <- catchZ(c2),
				  
				  // adds a subtype constraint on lower bounds
				  Constraint[SubstsT[Entity]] c3 <- { isCapturedTypeArgument(c2_.rh) ? {} : { c2_ }; },			  
				  Constraint[SubstsT[Entity]] c4 <- bindSl_(facts, mapper, subtype(c3.rh, c3.lh)) 
		   };
}

@doc{EXTENSION with wildcards}
public set[Constraint[SubstsT[Entity]]] catchCaptureVariable(c:violated(_)) = { c };
public default set[Constraint[SubstsT[Entity]]] catchCaptureVariable(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	Constraint[SubstsT[Entity]] c_ = runWithEmptySubsts(c);
	
	if(isBottom(c_.lh)) return {};
	
	bool lhIsCapturedTypeArg = isCapturedTypeArgument(c_.lh);
	bool rhIsCapturedTypeArg = isCapturedTypeArgument(c_.rh);
	
	bool lhIsTypeArgumentOfCastExpression = isTypeArgumentOfCastExpression(c_.lh);		
	if(lhIsTypeArgumentOfCastExpression)
		println("Special case of casts: <prettyprint(c_)>");
	
	if(!(lhIsCapturedTypeArg || rhIsCapturedTypeArg))
		return {};
	res = { *( { *( lhIsCapturedTypeArg ? 
								( { } + { *( rhIsCapturedTypeArg ? 
																	{ eq(cl.lh, cu.lh),
																	  eq(cl.rh, cu.rh),
																	  eq(cu.lh, cu.rh) } 
																	: {} ) 
															} 
								) 
								: ( rhIsCapturedTypeArg ? 
												( (lhIsTypeArgumentOfCastExpression) ? 
														{ 
												  		  subtype(cl.lh,cl.rh),
												  		  subtype(cu.rh,cu.lh)
														}
														:
														{
														  eq(cl.lh,cl.rh),
														  eq(cu.lh,cu.rh)
														} )
												: {} ) ) 
				} 
			  ) | Constraint[SubstsT[Entity]] cu  <- bindSu_(facts, mapper, c_),
				  Constraint[SubstsT[Entity]] cl  <- bindSl_(facts, mapper, c_)
		   };
	return res;
}

@doc{EXTENSION with wildcards}
public bool isBottom(TypeOf[Entity] v)
	= !isZero(bind(v, TypeOf[Entity] (Entity v_) { 
					return isBottom(v_) ? returnT(v_) : tzero(); }));
public bool isBottom(SubstsT[Entity] v) = isBottom(eval(v));
public bool isBottom(SubstsTL[Entity] v) = isBottom(tauToSubstsT(v));

@doc{EXTENSION with wildcards}
public bool isLowerBoundTypeArgument(SubstsTL[Entity] v) 
	= !isZero(bind(v, SubstsTL[Entity] (Entity v_) { 
				return isLowerBoundTypeArgument(v_) ? returnSL(v_) : liftTL(tzero()); }));

@doc{EXTENSION with wildcards}
public bool isUpperBoundTypeArgument(SubstsTL[Entity] v) 
	= !isZero(bind(v, SubstsTL[Entity] (Entity v_) { 
				return isUpperBoundTypeArgument(v_) ? returnSL(v_) : liftTL(tzero()); }));

@doc{EXTENSION with wildcards}
public bool isCapturedTypeArgument(SubstsT[Entity] v) 
	= !isZero(bind(v, SubstsT[Entity] (Entity v_) { 
					return isCapturedTypeArgument(v_) ? returnS(v_) : lift(tzero()); }));
@doc{EXTENSION with wildcards}
public bool isCapturedTypeArgument(SubstsTL[Entity] v) 
	= !isZero(bind(v, SubstsTL[Entity] (Entity v_) { 
					return isCapturedTypeArgument(v_) ? returnSL(v_) : liftTL(tzero()); }));
@doc{EXTENSION with wildcards}
public bool isTypeArgumentOfCastExpression(SubstsT[Entity] v) 
	= !isZero(bind(v, SubstsT[Entity] (Entity v_) { 
					return isTypeArgumentOfCastExpression(v_) ? returnS(v_) : lift(tzero()); }));

