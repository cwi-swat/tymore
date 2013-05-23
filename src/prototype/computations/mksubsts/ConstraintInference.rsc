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

@doc{Evaluates the left and right hand side of a constraint;
	 Note: semantically, left- and right-hand side may be of the forms:
	 		(a) C (non-generic type); (b) C<...Ai...> (generic type); (c) A (type parameter); 
}
public set[Constraint[SubstsT[Entity]]] gevalc(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(gevalc(mapper, v), SubstsT[Entity] (Entity v_) {
								return returnS(eval(getGenV(mapper, v))); }); })(c) }; 

@doc{Binds type parameters ignoring the case of a type argument variable,
	 i.e. stops when bound to a type argument variable}
public set[Constraint[SubstsT[Entity]]] boundS_(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(boundS_(mapper, v), SubstsT[Entity] (Entity b) {
							return returnS(getGenV(mapper, b)); }); })(c) }; 

@doc{Binds type parameters and type argument variables}
public set[Constraint[SubstsT[Entity]]] boundS(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(boundS(mapper, v), SubstsT[Entity] (Entity b) {
							return returnS(getGenV(mapper, b)); }); })(c) }; 

@doc{Computes the supertype predicate of the left-hand side given the right-hand side}				
public set[Constraint[SubstsT[Entity]]] supertypec(CompilUnit facts, Mapper mapper, Constraint::subtype(SubstsT[Entity] lh, SubstsT[Entity] rh))
	= { subtype(bind(discard(rh), SubstsT[Entity] (Entity v2) { 
						return bind(lh, SubstsT[Entity] (Entity v1) {
								SubstsT[bool] isSup = tauInv(supertypec_(facts, mapper, <v1, v2>)); 
								// DEBUG: 
								if(tzero() := eval(isSup)) println("<prettyprint(v1)> \<: <prettyprint(v2)> does not hold!");
								assert(!(tzero() := eval(isSup))); // makes sure that the supertype is found
								return bind(isSup, SubstsT[Entity] (bool b) { 
									return returnS(v2); }); }); }),
				rh) };
public set[Constraint[SubstsT[Entity]]] supertypec(CompilUnit facts, Mapper mapper, c:Constraint::eq(SubstsT[Entity] lh, SubstsT[Entity] rh)) 
	= { c };

@doc{Infers additional type constraints from subtype constraints}
public set[Constraint[SubstsT[Entity]]] inferTypeArguments(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	cons = {  c2 | Constraint[SubstsT[Entity]] c1  <- gevalc(facts, mapper, c),
				   Constraint[SubstsT[Entity]] c2  <- boundS_(facts, mapper, c1) 
		   };
		   
	return { *catchTypeArgVariable(c1) | Constraint[SubstsT[Entity]] c1 <- cons } 
		   + 
		   { *subtyping(facts, mapper, c2_)
				| Constraint[SubstsT[Entity]] c1 <- cons,
				  Constraint[SubstsT[Entity]] c2 <- boundS(facts, mapper, c1),
				  Constraint[SubstsT[Entity]] c2_  <- catchZ(c2) // zero may occur due to raw types
	  	   };
}
@doc{***Recursive subtyping with regard to type arguments}
public set[Constraint[SubstsT[Entity]]] subtyping(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	return { *( subtyping(facts, mapper, c3_) + { c3_ } ) 
				| Constraint[SubstsT[Entity]] c1  <- boundS(facts, mapper, c), 
				  Constraint[SubstsT[Entity]] c1_ <- catchZ(c1),
				  
				  Constraint[SubstsT[Entity]] c2  <- supertypec(facts, mapper, c1_),
				  Constraint[SubstsT[Entity]] c2_ <- catchZ(c2), 
				  
				  Constraint[SubstsT[Entity]] c3  <- invariant(facts, mapper, c2_),
				  Constraint[SubstsT[Entity]] c3_ <- catchZ(c3) 
		   };
}

@doc{Invariant function that imposes equality constraints on type arguments}
public set[Constraint[SubstsT[Entity]]] invariant(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	return { *catchTypeArgVariable(c2) // adds only constraints that have type argument variables
					| Entity rv <- tau(eval(c.rh)),
					  Entity param <- getTypeParamsOrArgs(getGenV(mapper, rv)), 
					  Constraint[SubstsT[Entity]] c1 := apply(SubstsT[Entity] (Entity _) { return returnS(param); })(c),
					  Constraint[SubstsT[Entity]] c2  <- boundS_(facts, mapper, eq(c1.lh, c1.rh)) 
		   };
}

public set[Constraint[SubstsT[Entity]]] catchTypeArgVariable(Constraint[SubstsT[Entity]] c) {
	TypeOf[tuple[Entity,Entity]] v = bind(eval(c.lh), TypeOf[tuple[Entity, Entity]] (Entity lv) {
										 return isTypeArgument(lv) ? tzero()
						   		  								   : bind(eval(c.rh), TypeOf[tuple[Entity, Entity]] (Entity rv) { 
						   												 return isTypeArgument(rv) ? tzero() : returnT(<lv,rv>); }); });
	return isZero(v) ? { c } : {};
}

/*
@doc{EXTENSION with wildcards: overrides the left hand side evaluation to account for wildcards}
public set[Constraint[SubstsT[Entity]]] gevalc(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(gevalc(mapper, v), SubstsT[Entity] (Entity v_) {
								return returnS(eval(getGenV(mapper, v))); }); },
			  SubstsT[Entity] (Entity v) { 
				return bind(gevalcR(mapper, v), SubstsT[Entity] (Entity v_) {
								return returnS(eval(getGenV(mapper, v))); }); })(c) }; 
*/
/*
@doc{EXTENSION with wildcards: extends the bind semantics to account for wildcards and splits it into the lower and upper bind semantics }
public set[Constraint[SubstsT[Entity]]] boundSu_(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(boundSu_(mapper, v), SubstsT[Entity] (Entity b) {
							return returnS(getGenV(mapper, b)); }); })(c) }; 
public set[Constraint[SubstsT[Entity]]] boundSu(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(boundSu(mapper, v), SubstsT[Entity] (Entity b) {
							return returnS(getGenV(mapper, b)); }); })(c) }; 
public set[Constraint[SubstsT[Entity]]] boundSl_(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(boundSl_(mapper, v), SubstsT[Entity] (Entity b) {
							return returnS(getGenV(mapper, b)); }); })(c) };
public set[Constraint[SubstsT[Entity]]] boundSl(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(boundSl(mapper, v), SubstsT[Entity] (Entity b) {
							return returnS(getGenV(mapper, b)); }); })(c) };
public set[Constraint[SubstsT[Entity]]] boundSul_(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(boundSu_(mapper, v), SubstsT[Entity] (Entity b) {
							return returnS(getGenV(mapper, b)); }); },
			  SubstsT[Entity] (Entity v) { 
				return bind(boundSl_(mapper, v), SubstsT[Entity] (Entity b) {
							return returnS(getGenV(mapper, b)); }); })(c) };
public set[Constraint[SubstsT[Entity]]] boundSul(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(boundSu(mapper, v), SubstsT[Entity] (Entity b) {
							return returnS(getGenV(mapper, b)); }); },
			  SubstsT[Entity] (Entity v) { 
				return bind(boundSl(mapper, v), SubstsT[Entity] (Entity b) {
							return returnS(getGenV(mapper, b)); }); })(c) };    
*/
/*
@doc{EXTENSION with wildcards: the inference function needs to use a different (lower and upper) bind semantics}
public set[Constraint[SubstsT[Entity]]] inferTypeArguments(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	cons = {  c2 | Constraint[SubstsT[Entity]] c1  <- gevalc(facts, mapper, c),
				   Constraint[SubstsT[Entity]] c2  <- boundSul_(facts, mapper, c1) 
		   };
		   
	return { *catchTypeArgVariable(c1) | Constraint[SubstsT[Entity]] c1 <- cons } 
		   + 
		   { *subtyping(facts, mapper, c2_)
				| Constraint[SubstsT[Entity]] c1  <- cons,
				  Constraint[SubstsT[Entity]] c2  <- boundSul(facts, mapper, c1),
				  Constraint[SubstsT[Entity]] c2_ <- catchZ(c2) // zero may occur due to raw types
	  	   };	
}
*/
/*
@doc{EXTENSION with wildcards: extends the invariant function to also impose covariance and contravariance}
public set[Constraint[SubstsT[Entity]]] invariant(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	return { *catchCaptureVariable(facts, mapper, c2) // 
				| Entity rv <- tau(eval(c.rh)),
				  Entity param <- getTypeParamsOrArgs(getGenV(mapper, rv)), 
				  Constraint[SubstsT[Entity]] c1 := apply(SubstsT[Entity] (Entity _) { return returnS(param); })(c),
				  Constraint[SubstsT[Entity]] c2  <- boundS_(facts, mapper, eq(c1.lh, c1.rh)) 
		   } 
		   + covariant(facts, mapper, c) 
		   + contravariant(facts, mapper, c);
}
*/
/*
@doc{EXTENSION with wildcards: adds constraints to account for covariance}
public set[Constraint[SubstsT[Entity]]] covariant(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	return { *catchTypeArgVariable(c2) // 
				| Entity rv <- tau(eval(c.rh)), 
				  Entity param <- getTypeParamsOrArgs(getGenV(mapper, rv)), 
				  Constraint[SubstsT[Entity]] c1 := apply(SubstsT[Entity] (Entity _) { return returnS(param); })(c),
					  
				  // adds a subtype constraint on upper bounds
				  Constraint[SubstsT[Entity]] c2  <- boundSu_(facts, mapper, subtype(c1.lh, c1.rh)) 
		   };
}
*/
/*
@doc{EXTENSION with wildcards: adds constraints to account for contravariance}
public set[Constraint[SubstsT[Entity]]] contravariant(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	return { *catchTypeArgVariable(c2) 
				| Entity rv <- tau(eval(c.rh)),
				  Entity param <- getTypeParamsOrArgs(getGenV(mapper, rhv)), 
				  Constraint[SubstsT[Entity]] c1 := apply(SubstsT[Entity] (Entity _) { return returnS(param); })(c),
					  
				  // adds a subtype constraint on lower bounds
				  Constraint[SubstsT[Entity]] c2  <- boundSl_(facts, mapper, subtype(c1.rh, c1.lh)) 
		   };
}
*/
/*
@doc{EXTENSION with wildcards}
public set[Constraint[SubstsT[Entity]]] catchCaptureVariable(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	TypeOf[tuple[bool,bool]] v = bind(eval(c.lh), TypeOf[tuple[bool,bool]] (Entity lv) {
									return bind(eval(c.rh), TypeOf[tuple[bool,bool]] (Entity rv) { 
						   						return returnT(<isCapturedTypeArgument(lv),isCapturedTypeArgument(rv)>); }); });
	
	return { *( { *(areCaptures.l ? 
						({ eq(cl_.lh, cu_.lh) } + { *(areCaptures.r ? { eq(cl_.rh, cu_.rh) } : {}) }) 
								  : (areCaptures.r ? 
										{ eq(cl_.rh, cu_.rh) } 
												  : {}) ) } 
			   + { *( (areCaptures.l && areCaptures.r) ? 
			   							{ eq(cl_.lh, cl_.rh) } + { eq(cu_.lh, cu_.rh) } 
			   				                          : {}) } ) 
			   				                          
			   		| tuple[bool l, bool r] areCaptures <- tau(v), 
			   		  (areCaptures.l || areCaptures.r), // at least one capture
			   		  
			   		  Constraint[SubstsT[Entity]] cu <- boundSu_(facts, mapper, c),
					  Constraint[SubstsT[Entity]] cu_ <- catchZ(cu),
					  
					  Constraint[SubstsT[Entity]] cl <- boundSl_(facts, mapper, c),
					  Constraint[SubstsT[Entity]] cl_ <- catchZ(cl) };
}
*/