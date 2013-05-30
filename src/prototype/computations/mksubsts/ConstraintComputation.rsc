@license{
  Copyright (c) 2009-2011 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - A.Izmaylova@cwi.nl}
module prototype::computations::mksubsts::ConstraintComputation

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import prototype::lang::java::jdt::refactorings::Java;
import prototype::lang::java::jdt::refactorings::JavaADT;
import prototype::lang::java::jdt::refactorings::JavaADTVisitor;
import prototype::lang::java::jdt::refactorings::PrettyPrintUtil;
import prototype::lang::java::jdt::refactorings::ValuesUtil;

import prototype::computations::mksubsts::BoundSemWithoutWildCards;
import prototype::computations::mksubsts::BoundSemWithWildCards;
import prototype::computations::mksubsts::LanguageInterface;
import prototype::computations::mksubsts::Monads;
import prototype::computations::mksubsts::TypeComputation;
import prototype::computations::mksubsts::FunctionsOfTypeValues;

import Prelude;
public data Constraint[&M] = eq(&M lh, &M rh)
					  		 | subtype(&M lh, &M rh)
					  		 | violated(str msg)
					  		 ;
					  		 
public set[Constraint[SubstsT[Entity]]] constrain(t:arrayAccess(_,_), CompilUnit facts, Mapper mapper) 
	= {};	
//public set[Constraint[SubstsT[Entity]]] constrain(t:arrayCreation(_, list[AstNode] _, some(AstNode initializer)), CompilUnit facts, Mapper mapper) 
//	= { subtype(glookupc(facts, mapper, rmv(initializer)), glookupc(facts, mapper, t)) }
//	;	
//public set[Constraint[SubstsT[Entity]]] constrain(t:arrayInitializer(list[AstNode] exprs), CompilUnit facts, Mapper mapper) 
//	= { subtype(glookupc(facts, mapper, rmv(expr)), glookupc(facts, mapper, t)) | expr <- exprs }
//	;	
public set[Constraint[SubstsT[Entity]]] constrain(t:assignment(AstNode _, nullLiteral()), CompilUnit facts, Mapper mapper) 
	= {};
public set[Constraint[SubstsT[Entity]]] constrain(t:assignment(AstNode lt, AstNode rt), CompilUnit facts, Mapper mapper) 
	= { subtype(glookupc(facts, mapper, rmv(rt)), glookupc(facts, mapper, rmv(lt))) }
	;
public set[Constraint[SubstsT[Entity]]] constrain(t:castExpression(_, AstNode e), CompilUnit facts, Mapper mapper) 
	= { (isDownCast(facts, mapper, t)) ? subtype(glookupc(facts, mapper, t), glookupc(facts, mapper, rmv(e))) 
									   : subtype(glookupc(facts, mapper, rmv(e)), glookupc(facts, mapper, t)) }
	;
public set[Constraint[SubstsT[Entity]]] constrain(t:classInstanceCreation(none(),_, [], [],_), CompilUnit facts, Mapper mapper) 
	= {};
public set[Constraint[SubstsT[Entity]]] constrain(t:classInstanceCreation(none(),_, [], list[AstNode] args,_), CompilUnit facts, Mapper mapper) 
	= { subtype(glookupc(facts, mapper, rmv(args[i])), bind(glookupc(facts, mapper, t), gparamc(i))) | int i <- [0..size(args)], args[i] != nullLiteral() }
	;
public set[Constraint[SubstsT[Entity]]] constrain(t:classInstanceCreation(some(AstNode e),_, [], list[AstNode] args, none()), CompilUnit facts, Mapper mapper) {
	if(isEmpty(args)) return {};
	return  { subtype(glookupc(facts, mapper, rmv(args[i])), bind(glookupc(facts, mapper, t), gparamc(i))) | int i <- [0..size(args)], args[i] != nullLiteral() } 
		  + { subtype(glookupc(facts, mapper, rmv(e)), bind(glookupc(facts, mapper, t), gdeclc)) };
}	
public set[Constraint[SubstsT[Entity]]] constrain(t:classInstanceCreation(_,_, [], list[AstNode] args, some(AstNode anonym)), CompilUnit facts, Mapper mapper) 
	= {};
public set[Constraint[SubstsT[Entity]]] constrain(t:conditionalExpression(AstNode _, AstNode thenBranch, AstNode elseBranch), CompilUnit facts, Mapper mapper) 
	=   { subtype(glookupc(facts, mapper, t), glookupc(facts, mapper, rmv(thenBranch))) }
	  + { subtype(glookupc(facts, mapper, t), glookupc(facts, mapper, rmv(elseBranch))) }
	;
public set[Constraint[SubstsT[Entity]]] constrain(t:constructorInvocation(_, list[AstNode] args), CompilUnit facts, Mapper mapper) {
	if(isEmpty(args)) return {};
	return { subtype(glookupc(facts, mapper, rmv(args[i])), bind(glookupc(facts, mapper, t), gparamc(i))) | int i <- [0..size(args)], args[i] != nullLiteral() };
}
public set[Constraint[SubstsT[Entity]]] constrain(t:fieldAccess(AstNode e,_), CompilUnit facts, Mapper mapper) 
	= { eq(glookupc(facts, mapper, rmv(e)), bind(glookupc(facts, mapper, t), gdeclc)) }
	;
public set[Constraint[SubstsT[Entity]]] constrain(t:methodInvocation(none(),_,_, list[AstNode] args), CompilUnit facts, Mapper mapper) {
	if(isEmpty(args)) return {};
	return { subtype(glookupc(facts, mapper, rmv(args[i])), bind(glookupc(facts, mapper, t), gparamc(i))) | int i <- [0..size(args)], args[i] != nullLiteral() };
}
public set[Constraint[SubstsT[Entity]]] constrain(t:methodInvocation(some(AstNode e),_,_, list[AstNode] args), CompilUnit facts, Mapper mapper) { 
	set[Constraint[SubstsT[Entity]]] cons = { subtype(glookupc(facts, mapper, rmv(e)), bind(glookupc(facts, mapper, t), gdeclc)) };
	if(isEmpty(args)) return cons; 
	set[Constraint[SubstsT[Entity]]] cons_ = { subtype(glookupc(facts, mapper, rmv(args[i])), bind(glookupc(facts, mapper, t), gparamc(i))) | int i <- [0..size(args)], args[i] != nullLiteral() };
	return cons + cons_;
}
public set[Constraint[SubstsT[Entity]]] constrain(t:qualifiedName(_,_), CompilUnit facts, Mapper mapper) 
	= {};
public set[Constraint[SubstsT[Entity]]] constrain(t:superConstructorInvocation(some(AstNode e), _, list[AstNode] args), CompilUnit facts, Mapper mapper) {
	set[Constraint[SubstsT[Entity]]] cons = { subtype(glookupc(facts, mapper, rmv(e)), bind(glookupc(facts, mapper, t), gdeclc)) };
	if(isEmpty(args)) return cons;
	set[Constraint[SubstsT[Entity]]] cons_ = { subtype(glookupc(facts, mapper, rmv(args[i])), bind(lookup(facts, mapper, t), gparamc(i))) | int i <- [0..size(args)], args[i] != nullLiteral() };
	return cons + cons_;
}
public set[Constraint[SubstsT[Entity]]] constrain(t:superFieldAccess(_,_), CompilUnit facts, Mapper mapper) 
	= {};
public set[Constraint[SubstsT[Entity]]] constrain(t:superMethodInvocation(_,_,_, list[AstNode] args), CompilUnit facts, Mapper mapper) {
	if(isEmpty(args)) return {};
	return { subtype(glookupc(facts, mapper, rmv(args[i])), bind(glookupc(facts, mapper, t), gparamc(i))) | int i <- [0..size(args)], args[i] != nullLiteral() };
}
public set[Constraint[SubstsT[Entity]]] constrain(t:singleVariableDeclaration(str name,_,_, some(nullLiteral()),_), CompilUnit facts, Mapper mapper) 
	= {};
public set[Constraint[SubstsT[Entity]]] constrain(t:singleVariableDeclaration(str name,_,_, some(AstNode initializer),_), CompilUnit facts, Mapper mapper) 
	= { subtype(glookupc(facts, mapper, rmv(initializer)), glookupc(facts, mapper, setAnnotations(simpleName(name), getAnnotations(t)))) }
	;
public set[Constraint[SubstsT[Entity]]] constrain(t:variableDeclarationFragment(str name, some(nullLiteral())), CompilUnit facts, Mapper mapper) 
	= {};
public set[Constraint[SubstsT[Entity]]] constrain(t:variableDeclarationFragment(str name, some(AstNode initializer)), CompilUnit facts, Mapper mapper) 
	= { subtype(glookupc(facts, mapper, rmv(initializer)), glookupc(facts, mapper, setAnnotations(simpleName(name), getAnnotations(t)))) }
	;
public default set[Constraint[SubstsT[Entity]]] constrain(AstNode t, CompilUnit facts, Mapper mapper) = {};

public bool isDownCast(CompilUnit facts, Mapper mapper, t:castExpression(_, AstNode e)) {
	TypeOf[bool] b = eval(tauInv(supertypec_(facts, mapper, <getType(t), getType(e)>)));
	if(isZero(b)) return false;
	return true;
}

@doc{Applies the same type computation function to the left and right of a constraint}
public Constraint[SubstsT[&T1]] (Constraint[SubstsT[&T]]) apply(SubstsT[&T1] (&T) f) 
	= Constraint[SubstsT[&T1]] (Constraint[SubstsT[&T]] c) {
			switch(c) {
				case subtype(SubstsT[&T] lh, SubstsT[&T] rh): return Constraint::subtype(bind(lh, f), bind(rh, f));
				case eq(SubstsT[&T] lh, SubstsT[&T] rh): return Constraint::eq(bind(lh, f), bind(rh, f));
			}
	  }; 

@doc{Applies different type computation functions to the left and right of a constraint that should preserve the type of a constraint}	  
public Constraint[SubstsT[&T1]] (Constraint[SubstsT[&T]]) apply(SubstsT[&T1] (&T) f1, SubstsT[&T1] (&T) f2) 
	= Constraint[SubstsT[&T1]] (Constraint[SubstsT[&T]] c) {
			switch(c) {
				case subtype(SubstsT[&T] lh, SubstsT[&T] rh): return Constraint::subtype(bind(lh, f1), bind(rh, f2));
				case eq(SubstsT[&T] lh, SubstsT[&T] rh): return Constraint::eq(bind(lh, f1), bind(rh, f2));
			}
	  }; 
	  
@doc{Catches zero computation at the right or left of a constraint and discard this constraint}
public set[Constraint[SubstsT[&T]]] catchZ(Constraint[SubstsT[&T]] c:violated(_)) = { c };
public default set[Constraint[SubstsT[&T]]] catchZ(Constraint[SubstsT[&T]] c) {
	Constraint[SubstsT[&T]] c_ = runWithEmptySubsts(c);
	return (isZero(c_.lh) || isZero(c_.rh)) ? {} : { c_ };
}

public Constraint[SubstsT[&T]] runWithEmptySubsts(Constraint[SubstsT[&T]] c:violated(str msg)) = c;
public Constraint[SubstsT[&T]] runWithEmptySubsts(Constraint::subtype(SubstsT[&T] lh, SubstsT[&T] rh)) = Constraint::subtype(runWithEmptySubsts(lh), runWithEmptySubsts(rh));
public Constraint[SubstsT[&T]] runWithEmptySubsts(Constraint::eq(SubstsT[&T] lh, SubstsT[&T] rh)) = Constraint::eq(runWithEmptySubsts(lh), runWithEmptySubsts(rh));	  

public Constraint[SubstsTL[&T]] tauToSubstsTL(Constraint[SubstsT[&T]] c:violated(str msg)) = violated(msg);
public Constraint[SubstsTL[&T]] tauToSubstsTL(Constraint::subtype(SubstsT[&T] lh, SubstsT[&T] rh))
	= Constraint::subtype(tauToSubstsTL(lh), tauToSubstsTL(rh));
public Constraint[SubstsTL[&T]] tauToSubstsTL(Constraint::eq(SubstsT[&T] lh, SubstsT[&T] rh))
	= Constraint::eq(tauToSubstsTL(lh), tauToSubstsTL(rh));
	
public Constraint[SubstsT[&T]] tauToSubstsT(Constraint::subtype(SubstsTL[&T] lh, SubstsTL[&T] rh))
	= Constraint::subtype(tauToSubstsT(lh), tauToSubstsT(rh));
public Constraint[SubstsT[&T]] tauToSubstsT(Constraint::eq(SubstsTL[&T] lh, SubstsTL[&T] rh))
	= Constraint::eq(tauToSubstsT(lh), tauToSubstsT(rh));


@doc{Prettyprinting facilities}
public str prettyprint(Constraint::violated(str msg)) = msg;
public str prettyprint(Constraint::eq(&M lh, &M rh)) = "<prettyprint(lh)> == <prettyprint(rh)>"; 
public str prettyprint(Constraint::subtype(&M lh, &M rh)) = "<prettyprint(lh)> \<: <prettyprint(rh)>"; 

