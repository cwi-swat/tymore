@license{
  Copyright (c) 2009-2012 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - A.Izmaylova@cwi.nl}
module prototype::computations::mksubsts::LanguageInterface

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import prototype::lang::java::jdt::refactorings::Java;
import prototype::lang::java::jdt::refactorings::JavaADT;
import prototype::lang::java::jdt::refactorings::PrettyPrintUtil;
import prototype::lang::java::jdt::refactorings::ValuesUtil;

import IO;
import List;
import Set;

@doc{Basic lookup semantics, the typed terms are: expressions (e) and declarations (d)}
public Entity lookup(e:arrayAccess(_,_)) = getType(e);
public Entity lookup(e:arrayCreation(_,_,_)) = getType(e);
public Entity lookup(e:arrayInitializer(_)) = getType(e);
public Entity lookup(e:assignment(AstNode le,_)) = lookup(le);
public Entity lookup(e:booleanLiteral(_)) = getType(e);
public Entity lookup(e:castExpression(_,_)) = entity([anonymous(e@location, getType(e))]);
public Entity lookup(e:characterLiteral(_)) = getType(e);
public Entity lookup(e:classInstanceCreation(_,_,_,_,_)) = e@bindings["methodBinding"];
public Entity lookup(e:conditionalExpression(_,_,_)) = getType(e); 
public Entity lookup(s:constructorInvocation(_,_)) = s@bindings["methodBinding"];
public Entity lookup(e:fieldAccess(_,_)) = e@bindings["variableBinding"]; 
public Entity lookup(e:infixExpression(_,_,_,_)) = getType(e);
public Entity lookup(e:instanceofExpression(_,_)) = getType(e);
public Entity lookup(e:markerAnnotation(_)) = getType(e);
public Entity lookup(e:methodInvocation(_,_,_,_)) = e@bindings["methodBinding"]; 
public Entity lookup(e:normalAnnotation(_,_)) = getType(e);
public Entity lookup(e:nullLiteral()) = getType(e);
public Entity lookup(e:numberLiteral(_)) = getType(e);
public Entity lookup(e:parenthesizedExpression(_)) = getType(e);
public Entity lookup(e:postfixExpression(_,_)) = getType(e);
public Entity lookup(e:prefixExpression(_,_)) = getType(e);
public Entity lookup(e:qualifiedName(qualifier,_)) = ("variableBinding" in e@bindings && !isArrayType(getType(qualifier))) ? e@bindings["variableBinding"] : getType(e);  
public Entity lookup(e:simpleName(_)) = ("variableBinding" in e@bindings && !isArrayType(getType(e))) ? e@bindings["variableBinding"] : getType(e); 
public Entity lookup(e:singleMemberAnnotation(_,_)) = getType(e);
public Entity lookup(e:stringLiteral(_)) = getType(e);
public Entity lookup(s:superConstructorInvocation(_,_,_)) = s@bindings["methodBinding"]; 
public Entity lookup(e:superFieldAccess(_,_)) = e@bindings["variableBinding"]; 
public Entity lookup(e:superMethodInvocation(_,_,_,_)) = e@bindings["methodBinding"]; 
public Entity lookup(e:thisExpression(_)) = getType(e); 
public Entity lookup(e:typeLiteral(_)) = getType(e); 
public Entity lookup(e:variableDeclarationExpression(_,_,_)) = getType(e); 
public Entity lookup(d:anonymousClassDeclaration(_)) = getType(d);
public Entity lookup(d:typeDeclaration(_,_,_,_,_,_,_)) = getType(d);
public Entity lookup(d:methodDeclaration(_,_,_,_,_,_,_)) = getType(d);
public Entity lookup(d:singleVariableDeclaration(_,_,_,_,_)) = d@bindings["variableBinding"];
public Entity lookup(d:variableDeclarationFragment(_,_)) = d@bindings["variableBinding"];
public default Entity lookup(AstNode t) { println("The term <t> does not have the lookup semantics!"); return zero(); }

@doc{Basic typing semantics}
public Entity getType(AstNode t) = t@bindings["typeBinding"];

@doc{Overrides semantics}
public set[Entity] overrides(CompilUnit facts, Entity v) = facts["overrides_func"][v];

@doc{Supertypes semantics}
public list[Entity] supertypes(CompilUnit facts, Entity v) { 
	list[Entity] sups = [ sup | Entity sup <- facts["supertypes_func"][v]]; 
	return isEmpty(sups) ? ( v != object() ? [ object() ] : [] ) : sups;
}

@doc{Static semantics}
public bool isStatic(CompilUnit facts, Entity v) { 
	isS = !isEmpty(facts["isStaticDecl_func"][v]);
	if(isS) println("static: " + v);
	return isS; 
}

@doc{Bound semantics}
public list[Entity] typeParamBounds(CompilUnit facts, Entity val) = [ v | <Entity k, Entity v> <- facts["bounds_func"], k == val];
