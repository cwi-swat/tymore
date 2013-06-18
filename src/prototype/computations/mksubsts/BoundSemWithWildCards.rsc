@license{
  Copyright (c) 2009-2011 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - A.Izmaylova@cwi.nl}
module prototype::computations::mksubsts::BoundSemWithWildCards

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import prototype::lang::java::jdt::refactorings::Java;
import prototype::lang::java::jdt::refactorings::JavaADT;
import prototype::lang::java::jdt::refactorings::PrettyPrintUtil;
import prototype::lang::java::jdt::refactorings::ValuesUtil;

import prototype::computations::mksubsts::BoundSemWithoutWildCards;
import prototype::computations::mksubsts::LanguageInterface;
import prototype::computations::mksubsts::Monads;
import prototype::computations::mksubsts::TypeComputation;
import prototype::computations::mksubsts::FunctionsOfTypeValues;


import IO;
import List;
import Map;
import Set;

@doc{EXTENSION with wildcards: the upper bind semantics that introduces new type argument variables and uses the extended bind semantics}
public SubstsT[Entity] boundSu(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str _)]))
	= bind(popSubsts(), SubstsT[Entity] (Substs s) {
			Entity b = lookupSubsts(s, tp);
			if(b == tp) return returnS(tp);
			return bind(pushSubsts(idS)(facts, mapper, b), SubstsT[Entity] (Entity b_) { 
						return boundSu(facts, mapper, b_); });
			});
public SubstsT[Entity] boundSu(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str name,_, init:entity([ *ids, wildcard() ]))])) // case of 'Ta'
	= boundSu(facts, mapper, entity( ids + ta + upper(boundEnv(facts, mapper, entity([ typeParameter(name) ]))) ));
public SubstsT[Entity] boundSu(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, init:entity([ *ids, wildcard(extends(Entity wcb)) ]))])) // case of 'Ta'
	= boundSu(facts, mapper, entity( ids + ta + upper(wcb) ));
public SubstsT[Entity] boundSu(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str name,_, init:entity([ *ids, wildcard(super(Entity wcb)) ]))])) // case of 'Ta'
	= boundSu(facts, mapper, entity( ids + ta + upper(boundEnv(facts, mapper, entity([ typeParameter(name) ]))) )); // there is always non-zero init
// ***Note: optimization in case of only inference of rawtypes
public SubstsT[Entity] boundSu(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, init:entity([]))])) // case of 'Ta'
	= boundSu(facts, mapper, entity( ids + ta + upper(init) ));
public SubstsT[Entity] boundSu(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, Entity init)])) // case of 'Ta'
	= boundS(facts, mapper, entity( ids + ta ));	
//public SubstsT[Entity] boundSu(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, Entity init)])) // case of 'Ta'
//	= boundSu(facts, mapper, entity( ids + ta + upper(init) ));
public SubstsT[Entity] boundSu(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(Entity _)])) // case of 'Ta_u'
	= boundS(facts, mapper, ta);
public SubstsT[Entity] boundSu(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(Entity _)])) // case of 'Ta_l'
	= boundS(facts, mapper, ta);

public SubstsT[Entity] boundSu(CompilUnit facts, Mapper mapper, entity([])) = lift(tzero());
public SubstsT[Entity] boundSu(CompilUnit facts, Mapper mapper, entity([ *ids, wildcard() ])) = returnS(object()); // wildcard value
public SubstsT[Entity] boundSu(CompilUnit facts, Mapper mapper, entity([ *ids, wildcard(extends(Entity wcb)) ])) // wildcard value
	= bind(pushSubsts(idS)(facts, mapper, wcb), SubstsT[Entity] (Entity _) { return boundSu(mapper, wcb); }); // wildcard value
public SubstsT[Entity] boundSu(CompilUnit facts, Mapper mapper, entity([ *ids, wildcard(super(Entity wcb)) ])) = returnS(object()); // wildcard value
public SubstsT[Entity] boundSu(CompilUnit facts, Mapper mapper, entity([ *ids, captureof(Entity wcd) ])) 
	= boundSu(facts, mapper, wcd); // capture value

public default SubstsT[Entity] boundSu(CompilUnit facts, Mapper mapper, Entity v) = returnS(v);
	
@doc{EXTENSION with wildcards: the lower bind semantics that introduces new type argument variables and uses the extended bind semantics}
public SubstsT[Entity] boundSl(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str _)]))
	= bind(popSubsts(), SubstsT[Entity] (Substs s) {
			Entity b = lookupSubsts(s, tp);
			if(b == tp) return returnS(tp);
			return bind(pushSubsts(idS)(facts, mapper, b), SubstsT[Entity] (Entity b_) { 
						return boundSl(facts, mapper, b_); });
			});
public SubstsT[Entity] boundSl(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, init:entity([ *ids, wildcard() ]))])) // case of 'Ta'
	= boundSl(facts, mapper, entity( ids + ta + lower(entity([ bottom() ])) ));
public SubstsT[Entity] boundSl(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, init:entity([ *ids, wildcard(extends(Entity wcb)) ]))])) // case of 'Ta'
	= boundSl(facts, mapper, entity( ids + ta + lower(entity([ bottom() ])) ));
public SubstsT[Entity] boundSl(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, init:entity([ *ids, wildcard(super(Entity wcb)) ]))])) // case of 'Ta'
	= boundSl(facts, mapper, entity( ids + ta + lower(wcb) ));	
// ***Note: optimization in case of only inference of rawtypes
public SubstsT[Entity] boundSl(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, init:entity([]))])) // case of 'Ta'
	= boundSl(facts, mapper, entity( ids + ta + lower(init)));
public SubstsT[Entity] boundSl(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, Entity init)])) // case of 'Ta'
	= boundS(facts, mapper, entity( ids + ta ));
//public SubstsT[Entity] boundSl(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, Entity init)])) // case of 'Ta'
//	= boundSl(facts, mapper, entity( ids + ta + lower(init)));
public SubstsT[Entity] boundSl(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(Entity _)])) // case of 'Ta_l'
	= boundS(facts, mapper, ta);
public SubstsT[Entity] boundSl(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(Entity _)])) // case of 'Ta_u'
	= boundS(facts, mapper, ta);

public SubstsT[Entity] boundSl(CompilUnit facts, Mapper mapper, entity([])) = lift(tzero());
public SubstsT[Entity] boundSl(CompilUnit facts, Mapper mapper, entity([ *ids, wildcard() ])) = returnS(entity([ bottom() ])); // wildcard value
public SubstsT[Entity] boundSl(CompilUnit facts, Mapper mapper, entity([ *ids, wildcard(extends(Entity wcb)) ])) = returnS(entity([ bottom() ])); // wildcard value
public SubstsT[Entity] boundSl(CompilUnit facts, Mapper mapper, entity([ *ids, wildcard(super(Entity wcb)) ])) // wildcard value
	= bind(pushSubsts(idS)(facts, mapper, wcb), SubstsT[Entity] (Entity _) { 
			return boundSl(facts, mapper, wcb); }); // wildcard value
public SubstsT[Entity] boundSl(CompilUnit facts, Mapper mapper, entity([ *ids, captureof(Entity wcd) ])) 
	= boundSl(facts, mapper, wcd); // capture value
	
public default SubstsT[Entity] boundSl(CompilUnit facts, Mapper mapper, Entity v) = returnS(v);
