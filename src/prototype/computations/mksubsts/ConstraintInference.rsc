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
import prototype::computations::mksubsts::BoundSemWithoutWildCards;
import prototype::computations::mksubsts::BoundSemWithWildCards;
import prototype::computations::mksubsts::LanguageInterface;
import prototype::computations::mksubsts::Monads;
import prototype::computations::mksubsts::TypeComputation;
import prototype::computations::mksubsts::FunctionsOfTypeValues;

import List;
import Map;
import Set;
import IO;

// FIXME: rename "boundS" -> "bindS"
// EXTEND: "boundS_" and "boundS" may return zero in case of raw types ***and*** free variables

//@doc{Evaluates the left and right hand side of a constraint;
//	 Note: semantically, left- and right-hand side may be of the forms:
//	 		(a) C (non-generic type); (b) C<...Ai...> (generic type); (c) A (type parameter); 
//}
//public set[Constraint[SubstsT[Entity]]] gevalc(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
//	= { apply(SubstsT[Entity] (Entity v) { 
//				return bind(gevalc(mapper, v), SubstsT[Entity] (Entity v_) {
//								return returnS(eval(getGenV(mapper, v))); }); })(c) }; 

@doc{Binds type parameters ignoring the case of a type argument variable,
	 i.e. stops when bound to a type argument variable}
public set[Constraint[SubstsT[Entity]]] boundS_(CompilUnit facts, Mapper mapper, c:violated(_)) = { c };
public default set[Constraint[SubstsT[Entity]]] boundS_(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(boundS_(mapper, v), SubstsT[Entity] (Entity b) {
							// ***Note: type value is a generic type value 
							Entity gen = getGenV(mapper, b);
							return isEmpty(getTypeParamsOrArgs(gen)) ? discard(returnS(gen)) : returnS(gen); }); })(c) }; 

@doc{Binds type parameters and type argument variables}
public set[Constraint[SubstsT[Entity]]] boundS(CompilUnit facts, Mapper mapper, c:violated(_)) = { c };
public default set[Constraint[SubstsT[Entity]]] boundS(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(boundS(mapper, v), SubstsT[Entity] (Entity b) {
							// ***Note: type value is a generic type value
							Entity gen = getGenV(mapper, b);
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
	return ( nonZero := catchZ(Constraint::eq(lh_, rh)) && !isEmpty(nonZero) ) ? nonZero : { Constraint::violated("Equality constraint does not hold!") } ;
}	
public set[Constraint[SubstsT[Entity]]] supertypec(CompilUnit facts, Mapper mapper, Constraint::subtype(SubstsT[Entity] lh, SubstsT[Entity] rh)) {
	lh = runWithEmptySubsts(lh);
	rh = runWithEmptySubsts(rh);
	
	lh_ = bind(rh, SubstsT[Entity] (Entity rv) { 
			return bind(lh, SubstsT[Entity] (Entity lv) {
						SubstsT[bool] isSup = tauInv(supertypec_(facts, mapper, <lv, rv>)); 
						return bind(isSup, SubstsT[Entity] (bool b) { 
									return returnS(rv); }); }); });
	// ***Note: violation of a constraint results in a zero computation
	return ( nonZero := catchZ(Constraint::subtype(lh_, rh)) && !isEmpty(nonZero) ) ? nonZero : { Constraint::violated("Subtype constraint does not hold!") };
}

//@doc{Infers additional type constraints from subtype constraints}
//public set[Constraint[SubstsT[Entity]]] inferTypeArguments(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
//	cons = { c2 | Constraint[SubstsT[Entity]] c1  <- gevalc(facts, mapper, c),
//			      Constraint[SubstsT[Entity]] c2  <- boundS_(facts, mapper, c1) 
//		   };
//		   
//	return { c4 | Constraint[SubstsT[Entity]] c1 <- cons,
//				  // adds only constraints that have type argument variables
//				  Constraint[SubstsT[Entity]] c2 <- catchTypeArgVariable(c1),
//				  // next two lines filter those, which represent nested raw types
//				  Constraint[SubstsT[Entity]] c3 <- bindTypeArgumentIfNotRawType(mapper, c2),
//				  Constraint[SubstsT[Entity]] c4 <- catchTypeArgVariable(c3) 
//		   } 
//		   + 
//		   { c3 | Constraint[SubstsT[Entity]] c1  <- cons,
//		   
//				  Constraint[SubstsT[Entity]] c2  <- boundS(facts, mapper, c1),
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
				 | Constraint[SubstsT[Entity]] c1  <- boundS(facts, mapper, c), 
				   Constraint[SubstsT[Entity]] c1_ <- catchZ(c1), // zero may occur, for example, due to raw types		
				      
				   Constraint[SubstsT[Entity]] c2  <- supertypec(facts, mapper, c1_), 	  
				   Constraint[SubstsT[Entity]] c3  <- invariant(facts, mapper, c2)
			};
			
	return { c4 | Constraint[SubstsT[Entity]] c1 <- constraints,
				  // adds only constraints that have type argument variables 
				  Constraint[SubstsT[Entity]] c2  <- catchTypeArgVariable(c1), 
				  // next two lines filter those, which represent nested raw types
				  Constraint[SubstsT[Entity]] c3  <- bindTypeArgumentIfNotRawType(mapper, c2),
				  Constraint[SubstsT[Entity]] c4  <- catchTypeArgVariable(c3)
		   }
		   +
		   { c2 | Constraint[SubstsT[Entity]] c1 <- constraints,  
		   		  // recur also on unconstrained type arguments to perform the check of subtyping wrt type arguments
				  Constraint[SubstsT[Entity]] c2 <- subtyping(facts, mapper, c1)
		   }
		   ;
}

@doc{Invariant function that imposes equality constraints on type arguments}
//public set[Constraint[SubstsT[Entity]]] invariant(CompilUnit facts, Mapper mapper, c:violated(_)) = { c };
//public default set[Constraint[SubstsT[Entity]]] invariant(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
//	return { c2_ | Entity rv    <- tau(eval(c.rh)),
//				   Entity param <- getTypeParamsOrArgs(getGenV(mapper, rv)), 
//				   Constraint[SubstsT[Entity]] c1  := apply(SubstsT[Entity] (Entity _) { return returnS(param); })(c),
//				   Constraint[SubstsT[Entity]] c1_ := eq(c1.lh, c1.rh), // turns into an equality constraint and adds it
//				   Constraint[SubstsT[Entity]] c2  <- boundS_(facts, mapper, c1_),
//				   Constraint[SubstsT[Entity]] c2_ <- catchZ(c2)
//		   };
//}

public set[Constraint[SubstsT[Entity]]] catchTypeArgVariable(c:violated(_)) = { c };
public default set[Constraint[SubstsT[Entity]]] catchTypeArgVariable(Constraint[SubstsT[Entity]] c) {
	Constraint[SubstsT[Entity]] c_ = runWithEmptySubsts(c);
	bool lhIsTypeArg = isTypeArgument(c_.lh);
	bool rhIsTypeArg = isTypeArgument(c_.rh);
	// Filters out constraints with the same type argument variable on both sides
	if(lhIsTypeArg && rhIsTypeArg 
			&& eval(c_.lh) == eval(c_.rh)) return {};
	if(lhIsTypeArg || rhIsTypeArg)
		return { c };
	return {};
}

public bool isTypeArgument(TypeOf[Entity] v)
	= !isZero(bind(v, TypeOf[Entity] (Entity v_) { 
					return isTypeArgument(v_) ? returnT(v_) : tzero(); }));
public bool isTypeArgument(SubstsT[Entity] v) = isTypeArgument(eval(v));
public bool isTypeArgument(SubstsTL[Entity] v) = isTypeArgument(tauToSubstsT(v));

public bool isLowerBoundTypeArgument(SubstsTL[Entity] v) 
	= !isZero(bind(v, SubstsTL[Entity] (Entity v_) { 
				return isLowerBoundTypeArgument(v_) ? returnSL(v_) : liftTL(tzero()); }));

public bool isUpperBoundTypeArgument(SubstsTL[Entity] v) 
	= !isZero(bind(v, SubstsTL[Entity] (Entity v_) { 
				return isUpperBoundTypeArgument(v_) ? returnSL(v_) : liftTL(tzero()); }));

public set[Constraint[SubstsT[Entity]]] bindTypeArgumentIfNotRawType(Mapper mapper, c:violated(_)) = { c };
public default set[Constraint[SubstsT[Entity]]] bindTypeArgumentIfNotRawType(Mapper mapper, Constraint[SubstsT[Entity]] c) {
	SubstsT[Entity] (Entity) f = SubstsT[Entity] (Entity v) {
									if(isTypeArgument(v)) {
										SubstsT[Entity] b = bind(boundS(mapper, v), SubstsT[Entity] (Entity b) { 
																// DEBUG: println("Bind type argument variables if not a raw type: <prettyprint(v)> <prettyprint(b)>"); 
																return returnS(getGenV(mapper, b)); });
										SubstsT[Entity] b_ = runWithEmptySubsts(b);
										if(!isZero(b_)) return b_;
										// ***Note: rawtypes specific optimization
										return discard(returnS(v));
									}
									return returnS(v);  };
	return { apply(f)(c) };
}

@doc{EXTENSION with wildcards: overrides the left hand side evaluation to account for wildcards}
public set[Constraint[SubstsT[Entity]]] gevalc(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(gevalc(mapper, v), SubstsT[Entity] (Entity v_) {
								return returnS(eval(getGenV(mapper, v))); }); },
			  SubstsT[Entity] (Entity v) { 
				return bind(gevalcNoCapture(mapper, v), SubstsT[Entity] (Entity v_) {
								return returnS(eval(getGenV(mapper, v))); }); })(c) }; 


@doc{EXTENSION with wildcards: extends the bind semantics to account for wildcards and splits it into the lower and upper bind semantics }
public set[Constraint[SubstsT[Entity]]] boundSu_(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(boundSu_(mapper, v), SubstsT[Entity] (Entity b) {
							// ***Note: type value is a generic type value
							Entity gen = getGenV(mapper, b);
							return isEmpty(getTypeParamsOrArgs(gen)) ? discard(returnS(gen)) : returnS(gen); }); })(c) }; 
public set[Constraint[SubstsT[Entity]]] boundSu(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(boundSu(mapper, v), SubstsT[Entity] (Entity b) {
							// ***Note: type value is a generic type value
							Entity gen = getGenV(mapper, b);
							return isEmpty(getTypeParamsOrArgs(gen)) ? discard(returnS(gen)) : returnS(gen); }); })(c) }; 
public set[Constraint[SubstsT[Entity]]] boundSl_(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(boundSl_(mapper, v), SubstsT[Entity] (Entity b) {
							// ***Note: type value is a generic type value
							Entity gen = getGenV(mapper, b);
							return isEmpty(getTypeParamsOrArgs(gen)) ? discard(returnS(gen)) : returnS(gen); }); })(c) };
public set[Constraint[SubstsT[Entity]]] boundSl(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(boundSl(mapper, v), SubstsT[Entity] (Entity b) {
							// ***Note: type value is a generic type value
							Entity gen = getGenV(mapper, b);
							return isEmpty(getTypeParamsOrArgs(gen)) ? discard(returnS(gen)) : returnS(gen); }); })(c) };
public set[Constraint[SubstsT[Entity]]] boundSul_(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(boundSu_(mapper, v), SubstsT[Entity] (Entity b) {
							// ***Note: type value is a generic type value
							Entity gen = getGenV(mapper, b);
							return isEmpty(getTypeParamsOrArgs(gen)) ? discard(returnS(gen)) : returnS(gen); }); },
			  SubstsT[Entity] (Entity v) { 
				return bind(boundSl_(mapper, v), SubstsT[Entity] (Entity b) {
							// ***Note: type value is a generic type value
							Entity gen = getGenV(mapper, b);
							return isEmpty(getTypeParamsOrArgs(gen)) ? discard(returnS(gen)) : returnS(gen); }); })(c) };
public set[Constraint[SubstsT[Entity]]] boundSul(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(boundSu(mapper, v), SubstsT[Entity] (Entity b) {
							// ***Note: type value is a generic type value
							Entity gen = getGenV(mapper, b);
							return isEmpty(getTypeParamsOrArgs(gen)) ? discard(returnS(gen)) : returnS(gen); }); },
			  SubstsT[Entity] (Entity v) { 
				return bind(boundSl(mapper, v), SubstsT[Entity] (Entity b) {
							// ***Note: type value is a generic type value
							Entity gen = getGenV(mapper, b);
							return isEmpty(getTypeParamsOrArgs(gen)) ? discard(returnS(gen)) : returnS(gen); }); })(c) };    


@doc{EXTENSION with wildcards: the inference function needs to use a different (lower and upper) bind semantics}
public set[Constraint[SubstsT[Entity]]] inferTypeArguments(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	cons = { runWithEmptySubsts(c2) 
				| Constraint[SubstsT[Entity]] c1  <- gevalc(facts, mapper, c),
			      Constraint[SubstsT[Entity]] c2  <- boundSul_(facts, mapper, c1) // ***Note: no capture values expected
		    };
		   
	return { c4 | Constraint[SubstsT[Entity]] c1 <- cons,
				  // adds only constraints that have type argument variables
				  Constraint[SubstsT[Entity]] c2 <- catchTypeArgVariable(c1),
				  // next two lines filter those, which represent nested raw types
				  Constraint[SubstsT[Entity]] c3 <- bindTypeArgumentIfNotRawType(mapper, c2),
				  Constraint[SubstsT[Entity]] c4 <- catchTypeArgVariable(c3) 
		   } 
		   + 
		   { c3 | Constraint[SubstsT[Entity]] c1  <- cons,
		   
				  Constraint[SubstsT[Entity]] c2  <- boundSul(facts, mapper, c1),
				  Constraint[SubstsT[Entity]] c2_ <- catchZ(c2), // zero may occur due to raw types
				  
				  Constraint[SubstsT[Entity]] c3  <- subtyping(facts, mapper, c2_)
	  	   };
}

@doc{EXTENSION with wildcards: extends the invariant function to also impose covariance and contravariance}
public set[Constraint[SubstsT[Entity]]] invariant(CompilUnit facts, Mapper mapper, c:violated(_)) = { c };
public set[Constraint[SubstsT[Entity]]] invariant(CompilUnit facts, Mapper mapper, Constraint::eq(SubstsT[Entity] lh, SubstsT[Entity] rh)) {
	return { c2_ | Entity rv    <- tau(eval(rh)),
			   	   Entity param <- getTypeParamsOrArgs(getGenV(mapper, rv)), 
			  
			       Constraint[SubstsT[Entity]] c1 := apply(SubstsT[Entity] (Entity _) { return returnS(param); })(Constraint::eq(lh,rh)),
			       Constraint[SubstsT[Entity]] c2  <- boundSu_(facts, mapper, c1) + boundSl_(facts, mapper, c1),
			       Constraint[SubstsT[Entity]] c2_ <- catchZ(c2)
	   };
}
public default set[Constraint[SubstsT[Entity]]] invariant(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	return { c3_ | Entity rv    <- tau(eval(c.rh)),
				   Entity param <- getTypeParamsOrArgs(getGenV(mapper, rv)), 
				  
				   Constraint[SubstsT[Entity]] c1 := apply(SubstsT[Entity] (Entity _) { return returnS(param); })(c),
				   Constraint[SubstsT[Entity]] c2  <- boundS_(facts, mapper, eq(c1.lh, c1.rh)), // ***Note: capture values could occur here
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
	bool lhIsCapturedTypeArg = isCapturedTypeArgument(c.lh);
	bool rhIsCapturedTypeArg = isCapturedTypeArgument(c.rh);
	if(lhIsCapturedTypeArg && rhIsCapturedTypeArg)
		return {};
	return { c2 | Entity rv    <- tau(eval(c.rh)), 
				  Entity param <- getTypeParamsOrArgs(getGenV(mapper, rv)),
				  
				  Constraint[SubstsT[Entity]] c1 := apply(SubstsT[Entity] (Entity _) { return returnS(param); })(c),
				  Constraint[SubstsT[Entity]] c2 <- boundSu_(facts, mapper, subtype(c1.lh, c1.rh)) // adds a subtype constraint on upper bounds
		   };
}

@doc{EXTENSION with wildcards: adds constraints to account for contravariance}
public set[Constraint[SubstsT[Entity]]] contravariant(CompilUnit facts, Mapper mapper, c:violated(_)) = { c };
public default set[Constraint[SubstsT[Entity]]] contravariant(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	bool lhIsCapturedTypeArg = isCapturedTypeArgument(c.lh);
	bool rhIsCapturedTypeArg = isCapturedTypeArgument(c.rh);
	if(lhIsCapturedTypeArg && rhIsCapturedTypeArg)
		return {};
	return { c2 | Entity rv    <- tau(eval(c.rh)),
				  Entity param <- getTypeParamsOrArgs(getGenV(mapper, rv)), 
				  
				  Constraint[SubstsT[Entity]] c1 := apply(SubstsT[Entity] (Entity _) { return returnS(param); })(c),
				  Constraint[SubstsT[Entity]] c2 <- boundSl_(facts, mapper, subtype(c1.rh, c1.lh)) // adds a subtype constraint on lower bounds 
		   };
}

@doc{EXTENSION with wildcards}
public set[Constraint[SubstsT[Entity]]] catchCaptureVariable(c:violated(_)) = { c };
public default set[Constraint[SubstsT[Entity]]] catchCaptureVariable(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	Constraint[SubstsT[Entity]] c_ = runWithEmptySubsts(c);
	bool lhIsCapturedTypeArg = isCapturedTypeArgument(c_.lh);
	bool rhIsCapturedTypeArg = isCapturedTypeArgument(c_.rh);
	if(!(lhIsCapturedTypeArg || rhIsCapturedTypeArg))
		return {};
	res = { *( { *( lhIsCapturedTypeArg ? 
								( { eq(cl.lh, cu.lh) } + { *( rhIsCapturedTypeArg ? 
																	{ eq(cl.rh, cu.rh),
																	
																	 // eq(cl.lh, cl.rh), // one should be sufficient
																	  eq(cu.lh, cu.rh) } 
																	: {} ) 
															} 
								) 
								: ( rhIsCapturedTypeArg ? 
												{ eq(cl.rh, cu.rh) } 
												: {} ) ) 
				} 
			  ) | Constraint[SubstsT[Entity]] cu  <- boundSu_(facts, mapper, c_),
				  Constraint[SubstsT[Entity]] cl  <- boundSl_(facts, mapper, c_)
		   };
	return res;
}

public bool isCapturedTypeArgument(SubstsT[Entity] v) 
	= !isZero(bind(v, SubstsT[Entity] (Entity v_) { 
					return isCapturedTypeArgument(v_) ? returnS(v_) : lift(tzero()); }));
