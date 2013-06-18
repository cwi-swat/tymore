@license{
  Copyright (c) 2009-2011 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - A.Izmaylova@cwi.nl}
module prototype::computations::mksubsts::BoundSemWithWildCards0

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import prototype::lang::java::jdt::refactorings::Java;
import prototype::lang::java::jdt::refactorings::JavaADT;
import prototype::lang::java::jdt::refactorings::PrettyPrintUtil;
import prototype::lang::java::jdt::refactorings::ValuesUtil;

import prototype::computations::mksubsts::BoundSemWithoutWildCards0;
import prototype::computations::mksubsts::LanguageInterface;
import prototype::computations::mksubsts::Monads;
import prototype::computations::mksubsts::TypeComputation;
import prototype::computations::mksubsts::FunctionsOfTypeValues;


import IO;
import List;
import Map;
import Set;

@doc{EXTENSION with wildcards: the upper bind semantics that introduces new type argument variables and uses the extended bind semantics}
public SubstsT[Entity] bindSu(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str _)]))
	= bind(popSubsts(), SubstsT[Entity] (Substs s) {
			Entity b = lookupSubsts(s, tp);
			if(b == tp || b == zero()) return returnS(tp);
			return bind(pushSubsts(idS)(facts, mapper, b), SubstsT[Entity] (Entity b_) { 
						return bindSu(facts, mapper, b_); });
			});
public SubstsT[Entity] bindSu(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str name,_, init:entity([ *ids, wildcard() ]))])) // case of 'Ta'
	= bindSu(facts, mapper, entity( ids + ta + upper(boundEnvWithNoCapture(facts, mapper, entity([ typeParameter(name) ]))) ));
public SubstsT[Entity] bindSu(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, init:entity([ *ids, wildcard(extends(Entity wcb)) ]))])) // case of 'Ta'
	= bindSu(facts, mapper, entity( ids + ta + upper(wcb) ));
public SubstsT[Entity] bindSu(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str name,_, init:entity([ *ids, wildcard(super(Entity wcb)) ]))])) // case of 'Ta'
	= bindSu(facts, mapper, entity( ids + ta + upper(boundEnvWithNoCapture(facts, mapper, entity([ typeParameter(name) ]))) ));
public SubstsT[Entity] bindSu(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, init:entity([]))])) // case of 'Ta'
	= bindSu(facts, mapper, entity( ids + ta + upper(init) ));
// ***Note: optimization in case of only inference of rawtypes
public SubstsT[Entity] bindSu(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity init)])) // case of 'Ta'
	= bindS(facts, mapper, ta); // optimization
public SubstsT[Entity] bindSu(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(Entity _)])) // case of 'Ta_u'
	= bindS(facts, mapper, ta);
public SubstsT[Entity] bindSu(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(Entity _)])) // case of 'Ta_l'
	= bindS(facts, mapper, ta);
	
// ***Note: explicit capturing
public SubstsT[Entity] bindSu(CompilUnit facts, Mapper mapper, ta:entity([ *_, captured(entity([ *ids, typeArgument(str _,_, Entity _), upper(Entity _)])) ])) // case of 'Ta_u'
	= bindS(facts, mapper, ta); // explicit capturing
public SubstsT[Entity] bindSu(CompilUnit facts, Mapper mapper, ta:entity([ *_, captured(entity([ *ids, typeArgument(str _,_, Entity _), lower(Entity _)])) ])) // case of 'Ta_l'
	= bindS(facts, mapper, ta); // explicit capturing

public SubstsT[Entity] bindSu(CompilUnit facts, Mapper mapper, entity([])) = lift(tzero());
public SubstsT[Entity] bindSu(CompilUnit facts, Mapper mapper, entity([ *ids, wildcard() ])) = lift(object()); // wildcard value
public SubstsT[Entity] bindSu(CompilUnit facts, Mapper mapper, entity([ *ids, wildcard(extends(Entity wcb)) ])) // wildcard value
	= bind(pushSubsts(idS)(facts, mapper, wcb), SubstsT[Entity] (Entity _) { return bindSu(mapper, wcb); }); // wildcard value
public SubstsT[Entity] bindSu(CompilUnit facts, Mapper mapper, entity([ *ids, wildcard(super(Entity wcb)) ])) = lift(object()); // wildcard value
public SubstsT[Entity] bindSu(CompilUnit facts, Mapper mapper, entity([ *ids, captureof(Entity wcd) ])) 
	= bindSu(facts, mapper, wcd); // capture value

public default SubstsT[Entity] bindSu(CompilUnit facts, Mapper mapper, Entity v) = returnS(v);

@doc{EXTENSION with wildcards: the upper bind semantics that introduces new type argument variables but does not bind type argument variables}
public SubstsT[Entity] bindSu_(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str _)]))
	= bind(popSubsts(), SubstsT[Entity] (Substs s) {
			Entity b = lookupSubsts(s, tp);
			if(b == tp || b == zero()) return returnS(tp);
			return bind(pushSubsts(idS)(facts, mapper, b), SubstsT[Entity] (Entity b_) { 
						return bindSu_(facts, mapper, b_); });
			});
public SubstsT[Entity] bindSu_(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str name,_, init:entity([ *ids, wildcard() ]))])) // case of 'Ta'
	= bindSu_(facts, mapper, entity( ids + ta + upper(boundEnvWithNoCapture(facts, mapper, entity([ typeParameter(name) ]))) ));
public SubstsT[Entity] bindSu_(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, init:entity([ *ids, wildcard(extends(Entity wcb)) ]))])) // case of 'Ta'
	= bindSu_(facts, mapper, entity( ids + ta + upper(wcb) ));
public SubstsT[Entity] bindSu_(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, init:entity([ *ids, wildcard(super(Entity wcb)) ]))])) // case of 'Ta'
	= bindSu_(facts, mapper, entity( ids + ta + upper(boundEnvWithNoCapture(facts, mapper, entity([ typeParameter(name) ]))) ));
public SubstsT[Entity] bindSu_(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, init:entity([]))])) // case of 'Ta'
	= bindSu_(facts, mapper, entity( ids + ta + upper(init)));
// ***Note: optimization in case of only inference of rawtypes
public SubstsT[Entity] bindSu_(CompilUnit facts, Mapper mapper, ta:entity([ *ids, ta:typeArgument(str _,_, Entity init)])) // case of 'Ta'
	= bindS_(facts, mapper, ta); // optimization
public SubstsT[Entity] bindSu_(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(Entity _)])) // case of 'Ta_u'
	= bindS_(facts, mapper, ta);
public SubstsT[Entity] bindSu_(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(Entity _)])) // case of 'Ta_l'
	= bindS_(facts, mapper, ta);
// ***Note: explicit capturing
public SubstsT[Entity] bindSu_(CompilUnit facts, Mapper mapper, ta:entity([ *_, captured(entity([ *ids, typeArgument(str _,_, Entity _), upper(Entity _)])) ])) // case of 'Ta_u'
	= bindS_(facts, mapper, ta); // explicit capturing
public SubstsT[Entity] bindSu_(CompilUnit facts, Mapper mapper, ta:entity([ *_, captured(entity([ *ids, typeArgument(str _,_, Entity _), lower(Entity _)])) ])) // case of 'Ta_l'
	= bindS_(facts, mapper, ta); // explicit capturing
public SubstsT[Entity] bindSu_(CompilUnit facts, Mapper mapper, entity([])) = lift(tzero());
public SubstsT[Entity] bindSu_(CompilUnit facts, Mapper mapper, entity([ *ids, wildcard() ])) = returnS(object()); // wildcard value
public SubstsT[Entity] bindSu_(CompilUnit facts, Mapper mapper, entity([ *ids, wildcard(extends(Entity wcb)) ])) // wildcard value
	= bind(pushSubsts(idS)(facts, mapper, wcb), SubstsT[Entity] (Entity _) { 
			return bindSu_(facts, mapper, wcb); }); // wildcard value
public SubstsT[Entity] bindSu_(CompilUnit facts, Mapper mapper, entity([ *ids, wildcard(super(Entity wcb)) ])) = returnS(object()); // wildcard value
public SubstsT[Entity] bindSu_(CompilUnit facts, Mapper mapper, entity([ *ids, captureof(Entity wcd) ])) 
	= bindSu_(facts, mapper, wcd); // capture value

public default SubstsT[Entity] bindSu_(CompilUnit facts, Mapper mapper, Entity v) = returnS(v);
	
@doc{EXTENSION with wildcards: the lower bind semantics that introduces new type argument variables and uses the extended bind semantics}
public SubstsT[Entity] bindSl(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str _)]))
	= bind(popSubsts(), SubstsT[Entity] (Substs s) {
			Entity b = lookupSubsts(s, tp);
			if(b == tp || b == zero()) return returnS(tp);
			return bind(pushSubsts(idS)(facts, mapper, b), SubstsT[Entity] (Entity b_) { 
						return bindSl(facts, mapper, b_); });
			});
public SubstsT[Entity] bindSl(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, init:entity([ *ids, wildcard() ]))])) // case of 'Ta'
	= bindSl(facts, mapper, entity( ids + ta + lower(entity([ bottom() ])) ));
public SubstsT[Entity] bindSl(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, init:entity([ *ids, wildcard(extends(Entity wcb)) ]))])) // case of 'Ta'
	= bindSl(facts, mapper, entity( ids + ta + lower(entity([ bottom() ])) ));
public SubstsT[Entity] bindSl(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, init:entity([ *ids, wildcard(super(Entity wcb)) ]))])) // case of 'Ta'
	= bindSl(facts, mapper, entity( ids + ta + lower(wcb) ));	
public SubstsT[Entity] bindSl(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, init:entity([]))])) // case of 'Ta'
	= bindSl(facts, mapper, entity( ids + ta + lower(init)));
// ***Note: optimization in case of only inference of rawtypes
public SubstsT[Entity] bindSl(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, Entity init)])) // case of 'Ta'
	= bindS(facts, mapper, entity( ids + ta )); // optimization
public SubstsT[Entity] bindSl(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(Entity _)])) // case of 'Ta_l'
	= bindS(facts, mapper, ta);
public SubstsT[Entity] bindSl(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(Entity _)])) // case of 'Ta_u'
	= bindS(facts, mapper, ta);
// ***Note: explicit capturing
public SubstsT[Entity] bindSl(CompilUnit facts, Mapper mapper, ta:entity([ *_, captured(entity([ *ids, typeArgument(str _,_, Entity _), lower(Entity _)])) ])) // case of 'Ta_l'
	= bindS(facts, mapper, ta); // explicit capturing
public SubstsT[Entity] bindSl(CompilUnit facts, Mapper mapper, ta:entity([ *_, captured(entity([ *ids, typeArgument(str _,_, Entity _), upper(Entity _)])) ])) // case of 'Ta_u'
	= bindS(facts, mapper, ta); // explicit capturing

public SubstsT[Entity] bindSl(CompilUnit facts, Mapper mapper, entity([])) = lift(tzero());
public SubstsT[Entity] bindSl(CompilUnit facts, Mapper mapper, entity([ *ids, wildcard() ])) = returnS(entity([ bottom() ])); // wildcard value
public SubstsT[Entity] bindSl(CompilUnit facts, Mapper mapper, entity([ *ids, wildcard(extends(Entity wcb)) ])) = returnS(entity([ bottom() ])); // wildcard value
public SubstsT[Entity] bindSl(CompilUnit facts, Mapper mapper, entity([ *ids, wildcard(super(Entity wcb)) ])) // wildcard value
	= bind(pushSubsts(idS)(facts, mapper, wcb), SubstsT[Entity] (Entity _) { 
			return bindSl(facts, mapper, wcb); }); // wildcard value
public SubstsT[Entity] bindSl(CompilUnit facts, Mapper mapper, entity([ *ids, captureof(Entity wcd) ])) 
	= bindSl(facts, mapper, wcd); // capture value
	
public default SubstsT[Entity] bindSl(CompilUnit facts, Mapper mapper, Entity v) = returnS(v);

@doc{EXTENSION with wildcards: the lower bind semantics that introduces new type argument variables but does not bind type argument variables}
public SubstsT[Entity] bindSl_(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str _)]))
	= bind(popSubsts(), SubstsT[Entity] (Substs s) {
			Entity b = lookupSubsts(s, tp);
			if(b == tp || b == zero()) return returnS(tp);
			return bind(pushSubsts(idS)(facts, mapper, b), SubstsT[Entity] (Entity b_) { 
						return bindSl_(facts, mapper, b_); });
			});
public SubstsT[Entity] bindSl_(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, init:entity([ *ids, wildcard() ]))])) // case of 'Ta'
	= bindSl_(facts, mapper, entity( ids + ta + lower(entity([ bottom() ])) ));
public SubstsT[Entity] bindSl_(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, init:entity([ *ids, wildcard(extends(Entity wcb)) ]))])) // case of 'Ta'
	= bindSl_(facts, mapper, entity( ids + ta + lower(entity([ bottom() ])) ));
public SubstsT[Entity] bindSl_(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, init:entity([ *ids, wildcard(super(Entity wcb)) ]))])) // case of 'Ta'
	= bindSl_(facts, mapper, entity( ids + ta + lower(wcb) ));
public SubstsT[Entity] bindSl_(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, init:entity([]))])) // case of 'Ta'
	= bindSl_(facts, mapper, entity( ids + ta + lower(init)));
// ***Note: optimization in case of only inference of rawtypes
public SubstsT[Entity] bindSl_(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, Entity init)])) // case of 'Ta'
	= bindS_(facts, mapper, entity( ids + ta )); // optimization
public SubstsT[Entity] bindSl_(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(Entity _)])) // case of 'Ta_l'
	= bindS_(facts, mapper, ta);
public SubstsT[Entity] bindSl_(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(Entity _)])) // case of 'Ta_u'
	= bindS_(facts, mapper, ta);
// ***Note: explicit capturing
public SubstsT[Entity] bindSl_(CompilUnit facts, Mapper mapper, ta:entity([ *_, captured(entity([ *ids, typeArgument(str _,_, Entity _), upper(Entity _)])) ])) // case of 'Ta_u'
	= bindS_(facts, mapper, ta); // explicit capturing
public SubstsT[Entity] bindSl_(CompilUnit facts, Mapper mapper, ta:entity([ *_, captured(entity([ *ids, typeArgument(str _,_, Entity _), lower(Entity _)])) ])) // case of 'Ta_l'
	= bindS_(facts, mapper, ta); // explicit capturing
public SubstsT[Entity] bindSl_(CompilUnit facts, Mapper mapper, entity([])) = lift(tzero());
public SubstsT[Entity] bindSl_(CompilUnit facts, Mapper mapper, entity([ *ids, wildcard() ])) = returnS(entity([ bottom() ])); // wildcard value
public SubstsT[Entity] bindSl_(CompilUnit facts, Mapper mapper, entity([ *ids, wildcard(extends(Entity wcb)) ])) = returnS(entity([ bottom() ])); // wildcard value
public SubstsT[Entity] bindSl_(CompilUnit facts, Mapper mapper, entity([ *ids, wildcard(super(Entity wcb)) ])) // wildcard value
	= bind(pushSubsts(idS)(facts, mapper, wcb), SubstsT[Entity] (Entity _) { 
			return bindSl_(facts, mapper, wcb); }); // wildcard value
public SubstsT[Entity] bindSl_(CompilUnit facts, Mapper mapper, entity([ *ids, captureof(Entity wcd) ])) 
	= bindSl_(facts, mapper, wcd); // capture value
	
public default SubstsT[Entity] bindSl_(CompilUnit facts, Mapper mapper, Entity v) = returnS(v);
