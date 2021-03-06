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
import Prelude;
import Set;

@doc{Base computations lifted to SubstsT}
public SubstsT[Entity] evalc(Entity v) = returnS(eval(v));
public SubstsT[Entity] lookupc(AstNode t) = returnS(lookup(t));

public SubstsT[Entity] gdeclc(Entity v) = returnS(decl(v));
public SubstsT[Entity] (Entity) gparamc(int i) = SubstsT[Entity] (Entity v) { return returnS(param(i)(v)); };

@doc{Evaluation in presence of plain generics}
public SubstsT[Entity] gevalc(CompilUnit facts, Mapper mapper, Entity v)
	= bind(evalc(v), SubstsT[Entity] (Entity vT) { 
			Entity vg = getGenV(facts, mapper, v);
			Entity vgT = eval(vg);
			if(vg == vgT) return returnS(vT);
			return bind(pushSubsts(paramSubstsWith(facts, mapper, vg))(facts, mapper, vgT), SubstsT[Entity] (Entity _) { 
						return returnS(vT); }); });

@doc{Lookup semantics}
public SubstsT[Entity] glookupc(CompilUnit facts, Mapper mapper, AstNode t)
	= bind(lookupc(t), SubstsT[Entity] (Entity v) { 
			return bind(catchZ(bind(subLookupc(facts, mapper, t), SubstsT[Entity] (Entity v0T) {
									SubstsT[bool] isSup = tauInv(supertypec_(facts, mapper, <v0T, eval(decl(v))>)); 
									// DEBUG: if(tzero() := eval(isSup)) println("SUPERTYPE: <prettyprint(vT_)> \<: <prettyprint(eval(decl(v)))>");
									assert(!(tzero() := eval(isSup))); 
									return bind(isSup, SubstsT[Entity] (bool b) {
												assert(b);
												return returnS(zero()); }); }), 
						  	   returnS(zero())), SubstsT[Entity] (Entity _) {
						  	   Substs s = getExprSubsts(facts, mapper, v);
						  	return bind(appnd(paramSubstsWith(facts, mapper, ("location" in getAnnotations(t)) ? <prettyprint(t), "<t@location.begin.line>; <t@location.begin.column>"> : <prettyprint(t)>)(s)), SubstsT[Entity] (value _) {
						  				return returnS(v); }); } ); });
//@doc{Contextual sublookup: t = t0.<...>}
//public SubstsT[Entity] subLookupc(CompilUnit facts, Mapper mapper, AstNode t)
//	= bind(lift(subterm(facts, mapper, t)), SubstsT[Entity] (AstNode t0) {
//			return bind(glookupc(facts, mapper, t0), SubstsT[Entity] (Entity v0) { 
//						return bind(gevalc(facts, mapper, v0), SubstsT[Entity] (Entity vT0) { 
//								return bind(bindLkp(facts, mapper, v0), SubstsT[Entity] (Entity _) {  
//										return lift(eval(boundEnv(facts, mapper, vT0))); }); }); }); });

@doc{Explicit substitution of type arguments locally scoped to a term}
public Substs getExprSubsts(CompilUnit facts, Mapper mapper, Entity v) {
	PEntity pv = mkSubsts(facts, mapper, v);
	if(pv.s == substs([],[])) return pv.s;
	list[Entity] params_ = getGenericTypes(pv.genval);
	if(isEmpty(params_)) return substs([],[]);
	list[Entity] params = pv.s.params;
	list[Entity] args = pv.s.args;
	list[Entity] args_ = [ args[i] | int i <- [0..size(params)], params[i] in params_ ];
	return substs(args_, params_);
}
	
//@doc{Lookup-bind semantics against explicit substitution or bounds of the global type environment;
//	the latter takes care of the cases when either the type parameter is not found in the substitution,
//	or it binds to a raw type}	
//public SubstsT[Entity] bindLkp(CompilUnit facts, Mapper mapper, Entity v) {
//	Entity vT = eval(getGenV(facts, mapper, v)); 
//	// DEBUG: tracer(true, "bindLkp: <prettyprint(vT)>; <prettyprint(v)>");
//	return catchZ(bindS(facts, mapper, vT), boundEnv(facts, mapper, vT));
//}

@doc{Supertype predicate that checks subtype relation}
public list[bool] supertype(CompilUnit facts, Mapper mapper, tuple[Entity l, Entity r] ts) {
	if(isSub(facts, mapper, ts.l, ts.r)) return [ true ];
	return [ b | Entity vS <- supertypes(facts, ts.l), 
		   		 bool b <- supertype(facts, mapper, <vS, ts.r>) ];
}

@doc{Simple way to take care of raw types, and wildcards; 
	 the assumption of initial program type correctness makes it sufficient for Java}
public default bool isSub(CompilUnit facts, Mapper mapper, Entity sub, Entity sup) = (mkSubsts(facts, mapper, sub).genval == mkSubsts(facts, mapper, sup).genval);

@doc{Computes ***direct*** supertypes}
public SubstsT_[Entity] supertypes_(CompilUnit facts, Mapper mapper, Entity v) {
	return bind(lift(supertypes(facts, v)), SubstsT_[Entity] (Entity vS1) { 
			return bind(lift(supertypes(facts, getGenV(facts, mapper, v))), SubstsT_[Entity] (Entity vS2) {
							if(getGenV(facts, mapper, vS1) != getGenV(facts, mapper, vS2)) return lift([]);
							return bind(tau(pushSubsts(paramSubstsWith(facts, mapper, inherits(getGenV(facts, mapper, v), vS2)))(facts, mapper, vS2)), SubstsT_[Entity] (Entity _) {
										return returnS_(vS1); }); }); });
}

@doc{Supertype predicate under substitution computation that checks subtype relation}
public SubstsT_[bool] supertypec_(CompilUnit facts, Mapper mapper, tuple[Entity l, Entity r] tpl) {
	if(isSub(facts, mapper, tpl.l, tpl.r)) return returnS_(true);
	return bind(supertypes_(facts, mapper, tpl.l), SubstsT_[bool] (Entity vS) { 
			return bind(supertypec_(facts, mapper, <vS, tpl.r>), SubstsT_[bool] (bool b) {
						return returnS_(b); }); });
}
//@doc{Supertype predicate under substitution computation that checks subtype relation: FACTORED OUT, see above}
//public SubstsT_[bool] supertypec_(CompilUnit facts, Mapper mapper, tuple[Entity, Entity] ts) {
//	if(ts[0] == object()) return returnS_(ts[0] == ts[1] ? true : false);
//	if(isSub(facts, mapper, ts[0],ts[1])) return returnS_(true);
//	return bind(lift(supertypes(facts, ts[0])), SubstsT_[bool] (Entity vS1) { 
//			return bind(supertypec_(facts, mapper, <vS1, ts[1]>), SubstsT_[bool] (bool b) {
//						if(!b) return lift([]);
//						return bind(lift(supertypes(facts, getGenV(facts, mapper, ts[0]))), SubstsT_[bool] (Entity vS2) { 
//									if(getGenV(facts, mapper, vS1) != getGenV(facts, mapper, vS2)) return lift([]);
//									return bind(tau(pushSubsts(paramSubstsWith(facts, mapper, inherits(getGenV(facts, mapper, ts[0]), vS2)))(facts, mapper, vS2)), SubstsT_[bool] (Entity _) { 
//												return returnS_(b); }); }); }); });
//}

@doc{A function that returns the lookup subterm}
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:classInstanceCreation(none(),_,[],_,none())) = tzero();
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:classInstanceCreation(some(AstNode expr),_,[],_,none())) = returnT(rmv(expr));
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:classInstanceCreation(_,_,[],_,some(AstNode anonymClass))) = tzero(); 
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:fieldAccess(AstNode expr,_)) 
	= isStatic(facts, lookup(e)) ? tzero() : returnT(rmv(expr)); 
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:methodInvocation(none(),_,_,_)) 
	= isStatic(facts, lookup(e)) ? tzero() : bind(scopec(facts, mapper, e), TypeOf[AstNode] (Entity scope) { 
													return returnT(thisExpression(none())[@bindings = ("typeBinding" : scope)]); });
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:methodInvocation(some(AstNode expr),_,_,_)) 
	= isStatic(facts, lookup(e)) ? tzero() : returnT(rmv(expr));
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:qualifiedName(AstNode qname,_)) 
	= isVariableBinding(lookup(e)) ? isStatic(facts, lookup(e)) ? tzero() : returnT(qname) : tzero(); 
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:simpleName(_)) 
	= (isFieldBinding(lookup(e)) && !isArrayType(getType(e))) 
		? isStatic(facts, lookup(e)) ? tzero() : bind(scopec(facts, mapper, e), TypeOf[AstNode] (Entity scope) { 
														return returnT(thisExpression(none())[@bindings = ("typeBinding" : scope)]); }) 
		: tzero();
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:superConstructorInvocation(none(),_,_)) 
	= bind(scopec(facts, mapper, e), TypeOf[AstNode] (Entity scope) { 
		return returnT(thisExpression(none())[@bindings = ("typeBinding" : scope)]); });
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:superConstructorInvocation(some(AstNode expr),_,_)) = returnT(rmv(expr));
public TypeOf[AstNode] subterm(CompilUnit facts, e:superFieldAccess(none(),_)) 
	= isStatic(facts, lookup(e)) ? tzero() : bind(scopec(facts, mapper, e), TypeOf[AstNode] (Entity scope) {
													return returnT(thisExpression(none())[@bindings = ("typeBinding" : scope)]); });
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:superFieldAccess(some(AstNode qualifier),_)) 
	= isStatic(facts, lookup(e)) ? tzero() : returnT(qualifier); 
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:superMethodInvocation(none(),_,_,_)) 
	= isStatic(facts, lookup(e)) ? tzero() : bind(scopec(facts, mapper, e), TypeOf[AstNode] (Entity scope) {
	 												return returnT(thisExpression(none())[@bindings = ("typeBinding" : scope)]); });
public TypeOf[AstNode] subterm(CompilUnit facts, Mapper mapper, e:superMethodInvocation(some(AstNode qualifier),_,_,_)) 
	= isStatic(facts, lookup(e)) ? tzero() : returnT(qualifier); 
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

@doc{EXTENSION with wildcards}
public bool isSub(CompilUnit facts, Mapper mapper, entity([ bottom() ]), Entity _) = true;

@doc{EXTENSION with wildcards: split of the evaluation semantics into 'left' (capturing) and 'right'} 
public SubstsT[Entity] gevalcNoCapture(CompilUnit facts, Mapper mapper, Entity v)
	= bind(evalc(v), SubstsT[Entity] (Entity vT) { 
			Entity vg = getGenV(facts, mapper, v);
			Entity vgT = eval(vg);
			if(vg == vgT) return returnS(vT);
			return bind(pushSubsts(paramSubstsWithNoCapture(facts, mapper, vg))(facts, mapper, vgT), SubstsT[Entity] (Entity _) { 
						return returnS(vT); }); });
						
@doc{EXTENSION with wildcards: extends/overrides the contextual sublookup to account for wildcards and captures}
@doc{Spec code:
public SubstsT[Entity] subLookupc(CompilUnit facts, Mapper mapper, AstNode t)
	= bind(subLookupc(facts, mapper, t), SubstsT[Entity] (Entity v0T) { 
			return lift(eval(boundEnv(facts, mapper, boundWildcardUB(v0T)))); });
}
public SubstsT[Entity] subLookupc(CompilUnit facts, Mapper mapper, AstNode t)
	= bind(lift(subterm(facts, mapper, t)), SubstsT[Entity] (AstNode t0) {
			return bind(glookupc(facts, mapper, t0), SubstsT[Entity] (Entity v0) { 
						return bind(gevalc(facts, mapper, v0), SubstsT[Entity] (Entity vT0) { 
								return bind(bindLkp(facts, mapper, v0), SubstsT[Entity] (Entity _) {  
										return lift(eval(boundEnv(facts, mapper, boundWildcardUB(vT0)))); }); }); }); });

@doc{EXTENSION with wildcards: overrides the lookup bind semantics to account for wildcards: the upper bind replaces the previous bind}
public SubstsT[Entity] bindLkp(CompilUnit facts, Mapper mapper, Entity v) {
	Entity vT = eval(getGenV(facts, mapper, v)); 
	// DEBUG: tracer(true, "bindLkp: <prettyprint(vT)>; <prettyprint(v)>");
	return catchZ(bindSu(facts, mapper, vT), boundEnv(facts, mapper, vT));
}

@doc{EXTENSION with wildcards}
public SubstsT[Entity] capture(CompilUnit facts, Mapper mapper, Entity v) {
	v = getGenV(facts, mapper, v);
	list[Entity] params = getTypeParamsOrArgs(v);
	if(isTypeArgument(v)) 
		return isCapturedTypeArgument(v) ? returnS(v) : returnS(capture(v)); // captured(_)
	if(isEmpty(params)) return returnS(v);
	return bind(popSubsts(), SubstsT[Entity] (Substs s) {
				list[Entity] args = [];
				for(int i <- [0..size(s.params)]) { 
					if(s.params[i] in params) {
						if(!(entity([ *_, captureof(_)]) := s.args[i])) 
							args = args + entity([ captureof(s.args[i]) ]);
						else args = args + s.args[i];
					} else {
						args = args + s.args[i];
					}
				}				
				return bind(appnd(substs(args, s.params)), SubstsT[Entity] (value _) {
							return returnS(v); }); });
}
@doc{EXTENSION with wildcards}
public SubstsT[Entity] uncapture(CompilUnit facts, Mapper mapper, Entity v) {
	v = getGenV(facts, mapper, v);
	if(isCapturedTypeArgument(v)) 
		return returnS(v.id[0].\type);
	return returnS(v);
}
