@license{
  Copyright (c) 2009-2011 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - A.Izmaylova@cwi.nl}
module prototype::computations::mksubsts::BoundSemWithoutWildCards0

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import prototype::lang::java::jdt::refactorings::Java;
import prototype::lang::java::jdt::refactorings::JavaADT;
import prototype::lang::java::jdt::refactorings::PrettyPrintUtil;
import prototype::lang::java::jdt::refactorings::ValuesUtil;

import prototype::computations::mksubsts::BoundSemWithWildCards0;
import prototype::computations::mksubsts::LanguageInterface;
import prototype::computations::mksubsts::Monads;
import prototype::computations::mksubsts::FunctionsOfTypeValues;

import IO;
import List;
import Map;
import Set;

// ***Note: bind semantics with no capturing

public Entity lookupEnv(CompilUnit facts, Entity v) {
	list[Entity] boundsOftp = typeParamBounds(facts, v);
	map[Entity, Entity] mapOfs = ();
	for(Entity tpb <- boundsOftp) mapOfs[v] = tpb;
	if(isEmpty(mapOfs)) mapOfs[v] = object();
	return mapOfs[v];
}

@doc{The bound semantics against a global type environment}
public SubstsT[Entity] boundEnv(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str name)]))
	= bind(pushSubsts(paramSubstsWith(facts, mapper, tp))(facts, mapper, lookupEnv(facts, tp)), SubstsT[Entity] (Entity b) {
			return boundEnv(facts, mapper, b); }); 	
public default SubstsT[Entity] boundEnv(CompilUnit facts, Mapper mapper, Entity v) = returnS(v);

@doc{The bind semantics against explicit substitution}
public SubstsT[Entity] bindS(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str _)]))
	= bind(popSubsts(), SubstsT[Entity] (Substs s) {
			Entity b = lookupSubsts(s, tp);
			if(b == tp || b == zero()) return returnS(tp);
			return bind(pushSubsts(idS)(facts, mapper, b), SubstsT[Entity] (Entity b_) { 
						return bindS(facts, mapper, b_); }); // recursive call to account for propagation through type parameters 
			});
public SubstsT[Entity] bindS(CompilUnit facts, Mapper mapper, entity([])) = lift(tzero());
public SubstsT[Entity] bindS(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, init:entity([]))])) // case of 'Ta'
	= lift(tzero());
public SubstsT[Entity] bindS(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity init)])) // case of 'Ta'
	= pushSubsts(paramSubstsWithNoCapture(facts, mapper, ta))(facts, mapper, init);
public default SubstsT[Entity] bindS(CompilUnit facts, Mapper mapper, Entity v) = returnS(v);

@doc{The bind semantics that does not bind type argument variables}
public SubstsT[Entity] bindS_(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str _)]))
	= bind(popSubsts(), SubstsT[Entity] (Substs s) {
			Entity b = lookupSubsts(s, tp);
			if(b == tp || b == zero()) return returnS(tp);
			return bind(pushSubsts(idS)(facts, mapper, b), SubstsT[Entity] (Entity b_) { 
						return bindS_(facts, mapper, b_); });
			});
public SubstsT[Entity] bindS_(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, entity([]))])) // case of 'Ta' with nonzero initial value
	= returnS(ta);
public SubstsT[Entity] bindS_(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity init)])) // case of 'Ta' with nonzero initial value
	= pushSubsts(paramSubstsWithNoCapture(facts, mapper, ta))(facts, mapper, init);
public SubstsT[Entity] bindS_(CompilUnit facts, Mapper mapper, entity([])) = lift(tzero());
public default SubstsT[Entity] bindS_(CompilUnit facts, Mapper mapper, Entity v) = returnS(v);

@doc{EXTENSION with wildcards: extends the bind semantics to account for wildcards, lower and upper bounds}
public SubstsT[Entity] bindS(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(init:entity([]))]))
	= lift(tzero());
public SubstsT[Entity] bindS(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(Entity init)]))
	= pushSubsts(paramSubstsWithNoCapture(facts, mapper, ta))(facts, mapper, init);
public SubstsT[Entity] bindS(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(init:entity([]))]))
	= lift(tzero());
public SubstsT[Entity] bindS(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(Entity init)]))
	= pushSubsts(paramSubstsWithNoCapture(facts, mapper, ta))(facts, mapper, init);
// ***Note: explicit capturing
public SubstsT[Entity] bindS(CompilUnit facts, Mapper mapper, entity([ *_, captured(ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(init:entity([]))])) ]))
	= lift(tzero());
public SubstsT[Entity] bindS(CompilUnit facts, Mapper mapper, entity([ *_, captured(ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(Entity init)])) ]))
	= pushSubsts(paramSubstsWith(facts, mapper, ta))(facts, mapper, init); // explicit capturing
public SubstsT[Entity] bindS(CompilUnit facts, Mapper mapper, entity([ *_, captured(ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(init:entity([]))])) ]))
	= lift(tzero());
public SubstsT[Entity] bindS(CompilUnit facts, Mapper mapper, entity([ *_, captured(ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(Entity init)])) ]))
	= pushSubsts(paramSubstsWith(facts, mapper, ta))(facts, mapper, init); // explicit capturing

@doc{EXTENSION with wildcards}
public SubstsT[Entity] bindS_(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(entity([]))]))
	= returnS(ta);
public SubstsT[Entity] bindS_(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(Entity init)]))
	= pushSubsts(paramSubstsWithNoCapture(facts, mapper, ta))(facts, mapper, init);
public SubstsT[Entity] bindS_(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(entity([]))]))
	= returnS(ta);
public SubstsT[Entity] bindS_(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(Entity init)]))
	= pushSubsts(paramSubstsWithNoCapture(facts, mapper, ta))(facts, mapper, init);
// ***Note: explicit capturing
public SubstsT[Entity] bindS_(CompilUnit facts, Mapper mapper, ta:entity([ *_, captured(entity([ *ids, typeArgument(str _,_, Entity _), upper(entity([]))])) ]))
	= returnS(ta); // explicit capturing
public SubstsT[Entity] bindS_(CompilUnit facts, Mapper mapper, entity([ *_, captured(ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(Entity init)])) ]))
	= pushSubsts(paramSubstsWith(facts, mapper, ta))(facts, mapper, init); // explicit capturing
public SubstsT[Entity] bindS_(CompilUnit facts, Mapper mapper, ta:entity([ *_, captured(entity([ *ids, typeArgument(str _,_, Entity _), lower(entity([]))])) ]))
	= returnS(ta); // explicit capturing
public SubstsT[Entity] bindS_(CompilUnit facts, Mapper mapper, entity([ *_, captured(ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(Entity init)])) ]))
	= pushSubsts(paramSubstsWith(facts, mapper, ta))(facts, mapper, init); // explicit capturing

@doc{EXTENSION with wildcards}
@doc{The bound semantics against a global type environment}
public SubstsT[Entity] boundEnvWithNoCapture(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str name)]))
	= bind(pushSubsts(paramSubstsWithNoCapture(facts, mapper, tp))(facts, mapper, lookupEnv(facts, tp)), SubstsT[Entity] (Entity b) {
			return boundEnvWithNoCapture(facts, mapper, b); }); 	
public default SubstsT[Entity] boundEnvWithNoCapture(CompilUnit facts, Mapper mapper, Entity v) = returnS(v);
