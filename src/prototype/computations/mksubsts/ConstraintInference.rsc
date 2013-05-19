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

//@doc{Evaluates the left and right hand side of a constraint}
public set[Constraint[SubstsT[Entity]]] gevalc(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(gevalc(mapper, v), SubstsT[Entity] (Entity v_) {
								return returnS(eval(getGenV(mapper, v))); }); })(c) }; 

@doc{Overrides the left hand side evaluation to account for wildcards}
public set[Constraint[SubstsT[Entity]]] gevalc(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(gevalc(mapper, v), SubstsT[Entity] (Entity v_) {
								return returnS(eval(getGenV(mapper, v))); }); },
			  SubstsT[Entity] (Entity v) { 
				return bind(gevalcRight(mapper, v), SubstsT[Entity] (Entity v_) {
								return returnS(eval(getGenV(mapper, v))); }); })(c) }; 

@doc{Binds type parameters ignoring cases of type argument variable}
public set[Constraint[SubstsT[Entity]]] boundS_(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return boundS_(mapper, v); })(c) }; 

@doc{Binds type parameters and type argument variables}
public set[Constraint[SubstsT[Entity]]] boundS(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return boundS(mapper, v); })(c) }; 

@doc{Extends the bind semantics to account for wildcards and splits it into the lower and upper bind semantics }
public set[Constraint[SubstsT[Entity]]] boundSu_(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return boundSu_(mapper, v); })(c) }; 
public set[Constraint[SubstsT[Entity]]] boundSu(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return boundSu(mapper, v); })(c) }; 
public set[Constraint[SubstsT[Entity]]] boundSl_(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return boundSl_(mapper, v); })(c) };
public set[Constraint[SubstsT[Entity]]] boundSl(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return boundSl(mapper, v); })(c) };
public set[Constraint[SubstsT[Entity]]] boundSul_(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return boundSu_(mapper, v); },
			  SubstsT[Entity] (Entity v) { 
				return boundSl_(mapper, v); })(c) };
public set[Constraint[SubstsT[Entity]]] boundSul(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return boundSu(mapper, v); },
			  SubstsT[Entity] (Entity v) { 
				return boundSl(mapper, v); })(c) };    

@doc{Computes the supertype predicate of the left hand side given the right hand side}				
public set[Constraint[SubstsT[Entity]]] supertypec(CompilUnit facts, Mapper mapper, Constraint::subtype(SubstsT[Entity] lh, SubstsT[Entity] rh))
	= { subtype(bind(discard(rh), SubstsT[Entity] (Entity v2) { 
						return bind(lh, SubstsT[Entity] (Entity v1) {
								SubstsT[bool] isSup = tauInv(supertypec_(facts, mapper, <v1, v2>)); assert(!(tzero() := eval(isSup)));
								return bind(isSup, SubstsT[Entity] (bool b) { assert(b);
									return returnS(v2); }); }); }),
				rh) };
public set[Constraint[SubstsT[Entity]]] supertypec(CompilUnit facts, Mapper mapper, c:Constraint::eq(SubstsT[Entity] lh, SubstsT[Entity] rh)) = { c };

//@doc{Infer additional type constraints from subtype constraints}
//public set[Constraint[SubstsT[Entity]]] inferTAs(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c)
//	= { * ( subtyping(facts, mapper, c___) + catchTaVars(c__1) ) | Constraint[SubstsT[Entity]] c_    <- gevalc(facts, mapper, c),
//														  		   Constraint[SubstsT[Entity]] c__1  <- boundS_(facts, mapper, c_),
//										                  		   Constraint[SubstsT[Entity]] c__2  <- boundS(facts, mapper, c__1),
//										                  		   Constraint[SubstsT[Entity]] c___  <- catchZ(c__2)};
@doc{Overrides the inference function to use the lower and upper bind semantics}
public set[Constraint[SubstsT[Entity]]] inferTAs(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c)
	= { * ( subtyping(facts, mapper, c___) + catchTaVars(c__1) ) | Constraint[SubstsT[Entity]] c_    <- gevalc(facts, mapper, c),
														  		   Constraint[SubstsT[Entity]] c__1  <- boundSul_(facts, mapper, c_),
										                  		   Constraint[SubstsT[Entity]] c__2  <- boundSul(facts, mapper, c__1),
										                  		   Constraint[SubstsT[Entity]] c___  <- catchZ(c__2)};

@doc{Subtyping with regard to type arguments}
public set[Constraint[SubstsT[Entity]]] subtyping(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	return { *( subtyping(facts, mapper, c3_) + { c3_ } ) | Constraint[SubstsT[Entity]] c1  <- boundS(facts, mapper, c), 
				   										    Constraint[SubstsT[Entity]] c1_ <- catchZ(c1),
				   										    Constraint[SubstsT[Entity]] c2  <- supertypec(facts, mapper, c1_),
				   										    Constraint[SubstsT[Entity]] c2_ <- catchZ(c2), 
				   										    Constraint[SubstsT[Entity]] c3  <- invariant(facts, mapper, c2_),
				   										    Constraint[SubstsT[Entity]] c3_ <- catchZ(c3) };
}

//@doc{Invariant function that imposes equality constraints on type arguments}
//public set[Constraint[SubstsT[Entity]]] invariant(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
//	if(typeof(Entity rhv) := eval(c.rh)) {
//		return { catchTaVars(c__) | Entity param <- getTypeParamsOrArgs(getGenV(mapper, rhv)), 
//					  Constraint[SubstsT[Entity]] c_ := apply(SubstsT[Entity] (Entity _) { return returnS(param); })(c),
//					  Constraint[SubstsT[Entity]] c__  <- boundS_(facts, mapper, eq(c_.lh, c_.rh)) };
//	}
//	return {};
//}

@doc{Overrides the invariant function to impose covariance and contravariance}
public set[Constraint[SubstsT[Entity]]] invariant(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	if(typeof(Entity rhv) := eval(c.rh)) {
		return { *catchCaptures(facts, mapper, c__) | Entity param <- getTypeParamsOrArgs(getGenV(mapper, rhv)), 
					   Constraint[SubstsT[Entity]] c_ := apply(SubstsT[Entity] (Entity _) { return returnS(param); })(c),
					   Constraint[SubstsT[Entity]] c__  <- boundS_(facts, mapper, eq(c_.lh, c_.rh)) } 
				+ covariant(facts, mapper, c) + contravariant(facts, mapper, c);
	}
	return {};
}

public set[Constraint[SubstsT[Entity]]] covariant(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	if(typeof(Entity rhv) := eval(c.rh)) {
		return { *catchTaVars(c__) | Entity param <- getTypeParamsOrArgs(getGenV(mapper, rhv)), 
					   Constraint[SubstsT[Entity]] c_ := apply(SubstsT[Entity] (Entity _) { return returnS(param); })(c),
					   Constraint[SubstsT[Entity]] c__  <- boundSu_(facts, mapper, subtype(c_.lh, c_.rh)) };
	}
	return {};
}

public set[Constraint[SubstsT[Entity]]] contravariant(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	if(typeof(Entity rhv) := eval(c.rh)) {
		return { *catchTaVars(c__) | Entity param <- getTypeParamsOrArgs(getGenV(mapper, rhv)), 
					                 Constraint[SubstsT[Entity]] c_ := apply(SubstsT[Entity] (Entity _) { return returnS(param); })(c),
					                 Constraint[SubstsT[Entity]] c__  <- boundSl_(facts, mapper, subtype(c_.rh, c_.lh)) };
	}
	return {};
}

public set[Constraint[SubstsT[Entity]]] catchCaptures(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	Constraint[SubstsT[Entity]] c_ = apply(SubstsT[Entity] (Entity v) { return returnS(v); }, SubstsT[Entity] (Entity v) { return isCapturedTypeArgument(v) ? returnS(v) : lift(tzero()); })(c);
	return { *(  { eq(cl_.lh, cu_.lh) } 
			   + { eq(cl_.rh, cu_.rh) } 
			   + { eq(cl_.lh, cl_.rh) }  
			   + { eq(cu_.lh, cu_.rh) } ) | Constraint[SubstsT[Entity]] c__ <- catchZ(c_),
											eval(c__.lh) != eval(c__.rh),
											Constraint[SubstsT[Entity]] cu <- boundSu_(facts, mapper, c__),
											Constraint[SubstsT[Entity]] cu_ <- catchZ(cu),
											Constraint[SubstsT[Entity]] cl <- boundSl_(facts, mapper, c__),
											Constraint[SubstsT[Entity]] cl_ <- catchZ(cl) };
}

public set[Constraint[SubstsT[Entity]]] catchTaVars(Constraint[SubstsT[Entity]] c) {
	if(typeof(Entity lh_) := eval(c.lh)) {
		if(typeof(Entity rh_) := eval(c.rh)) {
			if(isTypeArgument(lh_) || isTypeArgument(rh_)) return { c };
		}
	}	
	return {};
}

