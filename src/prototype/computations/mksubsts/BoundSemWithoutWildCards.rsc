@license{
  Copyright (c) 2009-2011 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - A.Izmaylova@cwi.nl}
module prototype::computations::mksubsts::BoundSemWithoutWildCards

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import prototype::lang::java::jdt::refactorings::Java;
import prototype::lang::java::jdt::refactorings::JavaADT;
import prototype::lang::java::jdt::refactorings::PrettyPrintUtil;
import prototype::lang::java::jdt::refactorings::ValuesUtil;

import prototype::computations::mksubsts::BoundSemWithWildCards;
import prototype::computations::mksubsts::LanguageInterface;
import prototype::computations::mksubsts::Monads;
import prototype::computations::mksubsts::FunctionsOfTypeValues;

import IO;
import List;
import Map;
import Set;

public Entity lookupEnv(CompilUnit facts, Entity v) {
	list[Entity] boundsOftp = typeParamBounds(facts, v);
	map[Entity, Entity] mapOfs = ();
	for(Entity tpb <- boundsOftp) mapOfs[v] = tpb;
	if(isEmpty(mapOfs)) mapOfs[v] = object();
	return mapOfs[v];
}

@doc{The bound semantics against a global type environment}
public SubstsT[Entity] boundEnv(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str name)]))
	= bind(pushSubsts(paramSubstsWith(mapper, tp))(mapper, lookupEnv(facts, tp)), SubstsT[Entity] (Entity b) {
			return boundEnv(facts, mapper, b); }); 	
public default SubstsT[Entity] boundEnv(CompilUnit facts, Mapper mapper, Entity v) = returnS(v);

@doc{The bind semantics against explicit substitution}
public SubstsT[Entity] boundS(Mapper mapper, tp:entity([ *ids, typeParameter(str _)]))
	= bind(popSubsts(), SubstsT[Entity] (Substs s) {
			Entity b = lookupSubsts(s, tp);
			if(b == tp) return returnS(tp);
			return bind(pushSubsts(idS)(mapper, b), SubstsT[Entity] (Entity b_) { 
						return boundS(mapper, b_); }); // recursive call to account for propagation through type parameters 
			});
public SubstsT[Entity] boundS(Mapper mapper, entity([])) = lift(tzero());
public SubstsT[Entity] boundS(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, init:entity([]))])) // case of 'Ta'
	= lift(tzero());
public SubstsT[Entity] boundS(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity init)])) // case of 'Ta'
	= pushSubsts(paramSubstsWith(mapper, ta))(mapper, init);
public default SubstsT[Entity] boundS(Mapper mapper, Entity v) = returnS(v);

@doc{The bind semantics that does not bind type argument variables}
public SubstsT[Entity] boundS_(Mapper mapper, tp:entity([ *ids, typeParameter(str _)]))
	= bind(popSubsts(), SubstsT[Entity] (Substs s) {
			Entity b = lookupSubsts(s, tp);
			if(b == tp) return returnS(tp);
			return bind(pushSubsts(idS)(mapper, b), SubstsT[Entity] (Entity b_) { 
						return boundS_(mapper, b_); });
			});
public SubstsT[Entity] boundS_(Mapper mapper, entity([])) = lift(tzero());
public default SubstsT[Entity] boundS_(Mapper mapper, Entity v) = returnS(v);

@doc{EXTENSION with wildcards: extends the bind semantics to account for wildcards, lower and upper bounds}
public SubstsT[Entity] boundS(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(init:entity([]))]))
	= lift(tzero());
public SubstsT[Entity] boundS(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(Entity init)]))
	= pushSubsts(paramSubstsWith(mapper, ta))(mapper, init);
public SubstsT[Entity] boundS(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(init:entity([]))]))
	= lift(tzero());
public SubstsT[Entity] boundS(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(Entity init)]))
	= pushSubsts(paramSubstsWith(mapper, ta))(mapper, init);

