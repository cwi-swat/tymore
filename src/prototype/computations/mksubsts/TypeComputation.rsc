@license{
  Copyright (c) 2009-2011 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - A.Izmaylova@cwi.nl}
module prototype::computations::mksubsts::TypeComputation

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import prototype::lang::java::jdt::refactorings::Java;
import prototype::lang::java::jdt::refactorings::JavaADT;
import prototype::lang::java::jdt::refactorings::PrettyPrintUtil;
import prototype::lang::java::jdt::refactorings::ValuesUtil;

import prototype::computations::mksubsts::BoundSemWithWildCards;
import prototype::computations::mksubsts::BoundSemWithoutWildCards;
import prototype::computations::mksubsts::LanguageInterface;
import prototype::computations::mksubsts::Monads;
import prototype::computations::mksubsts::FunctionsOfTypeValues;

import IO;
import List;
import Map;
import Set;

@doc{Base computations lifted to SubstsT}
public SubstsT[Entity] evalc(Entity v) = returnS(eval(v));
public SubstsT[Entity] lookupc(AstNode t) = returnS(lookup(t));

public SubstsT[Entity] gdeclc(Entity v) = returnS(decl(v));
public SubstsT[Entity] (Entity) gparamc(int i) = SubstsT[Entity] (Entity v) { return returnS(param(i)(v)); };

@doc{Evaluation in presence of plain generics}
public SubstsT[Entity] gevalc(Mapper mapper, Entity v)
	= bind(evalc(v), SubstsT[Entity] (Entity vT) { 
			Entity vg = getGenV(mapper, v);
			Entity vgT = eval(vg);
			if(vg == vgT) return returnS(vT);
			return bind(pushSubsts(paramSubstsWith(mapper, vg))(mapper, vgT), SubstsT[Entity] (Entity _) { 
						return returnS(vT); }); });

@doc{Split of the evaluation semantics into 'left' (capturing) and 'right'} 
public SubstsT[Entity] gevalcRight(Mapper mapper, Entity v)
	= bind(evalc(v), SubstsT[Entity] (Entity vT) { 
			Entity vg = getGenV(mapper, v);
			Entity vgT = eval(vg);
			if(vg == vgT) return returnS(vT);
			// TODO: right-hand side evaluation semantics, which should not capture wildcards
			return bind(pushSubsts(paramSubstsWithNoCapture(mapper, vg))(mapper, vgT), SubstsT[Entity] (Entity _) { 
						return returnS(vT); }); });

@doc{Lookup semantics}
public SubstsT[Entity] glookupc(CompilUnit facts, Mapper mapper, AstNode t)
	= bind(lookupc(t), SubstsT[Entity] (Entity v) { 
			return bind(catchZ(bind(subLookupc(facts, mapper, t), SubstsT[Entity] (Entity vT_) {
									SubstsT[bool] isSup = tauInv(supertypec_(facts, mapper, <vT_, eval(decl(v))>)); 
									// DEBUG: if(tzero() := eval(isSup)) println("SUPERTYPE: <prettyprint(vT_)> \<: <prettyprint(eval(decl(v)))>");
									assert(!(tzero() := eval(isSup))); 
									return bind(isSup, SubstsT[Entity] (bool b) {
												assert(b);
												return returnS(zero()); }); }), 
						  	   returnS(zero())), SubstsT[Entity] (Entity _) {
						  	   Substs s = getExprSubsts(mapper, v);
						  	return bind(appnd(paramSubstsWith(mapper, t)(s)), SubstsT[Entity] (value _) {
						  				return returnS(v); }); } ); });
@doc{Contextual sublookup}
public SubstsT[Entity] subLookupc(CompilUnit facts, Mapper mapper, AstNode t)
	= bind(lift(subterm(facts, mapper, t)), SubstsT[Entity] (AstNode t0) {
			return bind(glookupc(facts, mapper, t0), SubstsT[Entity] (Entity v0) { 
						return bind(gevalc(mapper, v0), SubstsT[Entity] (Entity vT0) { 
								return bind(boundLkp(facts, mapper, v0), SubstsT[Entity] (Entity _) { 
										return lift(eval(boundEnv(facts, mapper, vT0))); }); }); }); });

@doc{Overrides the contextual sublookup to account for wildcards and captures}
//public SubstsT[Entity] subLookupc(CompilUnit facts, Mapper mapper, AstNode t)
//	= bind(lift(subterm(facts, mapper, t)), SubstsT[Entity] (AstNode t_) {
//			return bind(glookupc(facts, mapper, t_), SubstsT[Entity] (Entity v_) { 
//						return bind(gevalc(mapper, v_), SubstsT[Entity] (Entity v__) { 
//								return bind(boundLkp(facts, mapper, v_), SubstsT[Entity] (Entity _) { 
//										return lift(eval(boundEnv(facts, mapper, boundWildcardUB(v__)))); }); }); }); });

@doc{Explicit substitution of type arguments locally scoped to a term}
public Substs getExprSubsts(Mapper mapper, Entity v) {
	PEntity pv = mkSubsts(mapper, v);
	if(pv.s == substs([],[])) return pv.s;
	list[Entity] params_ = getGenericTypes(pv.genval);
	if(isEmpty(params_)) return substs([],[]);
	list[Entity] params = pv.s.params;
	list[Entity] args = pv.s.args;
	list[Entity] args_ = [ args[i] | int i <- [0..size(params) - 1], params[i] in params_ ];
	return substs(args_, params_);
}
	
@doc{Lookup bind semantics against explicit substitution composed with the bound against type environment}	
public SubstsT[Entity] boundLkp(CompilUnit facts, Mapper mapper, Entity v) {
	Entity vT = eval(getGenV(mapper, v)); // tracer(true, "boundLkp: <prettyprint(vT)>; <prettyprint(v)>");
	return catchZ(boundS(mapper, vT), boundEnv(facts, mapper, vT));
}

@doc{Overrides the lookup bind semantics to account for wildcards: the upper bind replaces the previous bind}
//public SubstsT[Entity] boundLkp(CompilUnit facts, Mapper mapper, Entity v) {
//	Entity vT = eval(getGenV(mapper, v)); // tracer(true, "boundLkp: <prettyprint(vT)>; <prettyprint(v)>");
//	return catchZ(boundSu(mapper, vT), boundEnv(facts, mapper, vT));
//}

@doc{Supertype predicate that checks subtype relation}
public list[bool] supertype(CompilUnit facts, Mapper mapper, tuple[Entity, Entity] ts) {
	if(isSub(mapper, ts[0], ts[1])) return [ true ];
	return [ b | Entity vS <- supertypes(facts, ts[0]), 
		   		 bool b <- supertype(facts, mapper, <vS, ts[1]>) ];
}

@doc{Takes care of raw types, and wildcards}
public bool isSub(Mapper mapper, Entity sub, Entity sup) = (mkSubsts(mapper, sub).genval == mkSubsts(mapper, sup).genval);

@doc{Direct supertypes}
public SubstsT_[Entity] supertypes_(CompilUnit facts, Mapper mapper, Entity v) {
	return bind(lift(supertypes(facts, v)), SubstsT_[Entity] (Entity vS1) { 
			return bind(lift(supertypes(facts, getGenV(mapper, v))), SubstsT_[Entity] (Entity vS2) {
							if(getGenV(mapper, vS1) != getGenV(mapper, vS2)) return lift([]);
							return bind(tau(pushSubsts(paramSubstsWith(mapper, inherits(getGenV(mapper, v), vS2)))(mapper, vS2)), SubstsT_[Entity] (Entity _) {
										return returnS_(vS1); }); }); });
}

@doc{Supertype predicate under substitution computation that checks subtype relation}
public SubstsT_[bool] supertypec_(CompilUnit facts, Mapper mapper, tuple[Entity, Entity] ts) {
	if(isSub(mapper, ts[0], ts[1])) return returnS_(true);
	return bind(supertypes_(facts, mapper, ts[0]), SubstsT_[bool] (Entity vS) { 
			return bind(supertypec_(facts, mapper, <vS, ts[1]>), SubstsT_[bool] (bool b) {
						return returnS_(b); }); });
}
@doc{ (Factored out above) Supertype predicate under substitution computation that checks subtype relation}
//public SubstsT_[bool] supertypec_(CompilUnit facts, Mapper mapper, tuple[Entity, Entity] ts) {
//	if(ts[0] == object()) return returnS_(ts[0] == ts[1] ? true : false);
//	if(isSub(mapper, ts[0],ts[1])) return returnS_(true);
//	return bind(lift(supertypes(facts, ts[0])), SubstsT_[bool] (Entity vS1) { 
//			return bind(supertypec_(facts, mapper, <vS1, ts[1]>), SubstsT_[bool] (bool b) {
//						if(!b) return lift([]);
//						return bind(lift(supertypes(facts, getGenV(mapper, ts[0]))), SubstsT_[bool] (Entity vS2) { 
//									if(getGenV(mapper, vS1) != getGenV(mapper, vS2)) return lift([]);
//									return bind(tau(pushSubsts(paramSubstsWith(mapper, inherits(getGenV(mapper, ts[0]), vS2)))(mapper, vS2)), SubstsT_[bool] (Entity _) { 
//												return returnS_(b); }); }); }); });
//}

@doc{A function that returns the lookup subterm}
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:classInstanceCreation(none(),_,[],_,none())) = tzero();
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:classInstanceCreation(some(AstNode expr),_,[],_,none())) = returnT(rmv(expr));
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:classInstanceCreation(_,_,[],_,some(AstNode anonymClass))) = tzero(); 
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:fieldAccess(AstNode expr,_)) = returnT(rmv(expr)); 
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:methodInvocation(none(),_,_,_)) 
	= bind(scopec(facts, mapper, e), TypeOf[AstNode] (Entity scope) { 
			return returnT(thisExpression(none())[@bindings = ("typeBinding" : scope)]); });
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:methodInvocation(some(AstNode expr),_,_,_)) = returnT(rmv(expr));
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:qualifiedName(AstNode qname,_)) = (isVariableBinding(lookup(e))) ? returnT(qname) : tzero(); 
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:simpleName(_)) 
	= (isFieldBinding(lookup(e)) && !isArrayType(getType(e))) 
		? bind(scopec(facts, mapper, e), TypeOf[AstNode] (Entity scope) { 
				return returnT(thisExpression(none())[@bindings = ("typeBinding" : scope)]); }) 
		: tzero();
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:superConstructorInvocation(none(),_,_)) 
	= bind(scopec(facts, mapper, e), TypeOf[AstNode] (Entity scope) { 
		return returnT(thisExpression(none())[@bindings = ("typeBinding" : scope)]); });
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:superConstructorInvocation(some(AstNode expr),_,_)) = returnT(rmv(expr));
public TypeOf[AstNode] subterm(CompilUnit facts, e:superFieldAccess(none(),_)) 
	= bind(scopec(facts, mapper, e), TypeOf[AstNode] (Entity scope) {
		return returnT(thisExpression(none())[@bindings = ("typeBinding" : scope)]); });
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:superFieldAccess(some(AstNode qualifier),_)) = returnT(qualifier); 
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:superMethodInvocation(none(),_,_,_)) 
	= bind(scopec(facts, mapper, e), TypeOf[AstNode] (Entity scope) {
	 	return returnT(thisExpression(none())[@bindings = ("typeBinding" : scope)]); });
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:superMethodInvocation(some(AstNode qualifier),_,_,_)) = returnT(qualifier); 
public default TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, AstNode t) = tzero();

public AstNode rmv(parenthesizedExpression(AstNode expr)) = rmv(expr);
public default AstNode rmv(AstNode expr) = expr;

@doc{Imposed by the contextual semantics}
public TypeOf[Entity] scopec(CompilUnit facts, Mapper mapper, AstNode e) {
	list[Entity] scopes = [ scope | Entity scope <- e@scopes, 
									bool b <- supertype(facts, mapper, <scope, eval(decl(lookup(e)))>), 
									b ];
	// DEBUG: if(size(e@scopes) > 1) { println("NESTING : "); println(prettyprint(lookup(e))); for(Entity scope <- scopes) println("scope: " + prettyprint(scope)); }
	return tauInv(scopes);
}