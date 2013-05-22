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

@doc{The upper bind semantics that introduces new type argument variables and uses the extended bind semantics}
public SubstsT[Entity] boundSu(Mapper mapper, tp:entity([ *ids, typeParameter(str _)]))
	= bind(popSubsts(), SubstsT[Entity] (Substs s) {
			Entity b = lookupSubsts(s, tp);
			if(b == tp) return returnS(tp);
			return bind(pushSubsts(idS)(mapper, b), SubstsT[Entity] (Entity b_) { 
						return boundSu(mapper, b_); });
			});
public SubstsT[Entity] boundSu(Mapper mapper, entity([ *ids, ta:typeArgument(str _, _, entity([ *ids, wildcard() ]))])) // case of 'Ta'
	= boundSu(mapper, entity( ids + ta + upper(zero()) ));
public SubstsT[Entity] boundSu(Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, entity([ *ids, wildcard(extends(Entity wcb)) ]))])) // case of 'Ta'
	= boundSu(mapper, entity( ids + ta + upper(wcb) ));
public SubstsT[Entity] boundSu(Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, entity([ *ids, wildcard(super(Entity wcb)) ]))])) // case of 'Ta'
	= boundSu(mapper, entity( ids + ta + upper(zero()) ));
public SubstsT[Entity] boundSu(Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, Entity init)])) // case of 'Ta'
	= boundSu(mapper, entity( ids + ta + upper(init)));

public SubstsT[Entity] boundSu(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(Entity _)])) // case of 'Ta_u'
	= boundS(mapper, ta);
public SubstsT[Entity] boundSu(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(Entity _)])) // case of 'Ta_l'
	= boundS(mapper, ta);

public SubstsT[Entity] boundSu(Mapper mapper, entity([])) = lift(tzero());
public SubstsT[Entity] boundSu(Mapper mapper, entity([ *ids, wildcard() ])) = lift(tzero());
public SubstsT[Entity] boundSu(Mapper mapper, entity([ *ids, wildcard(extends(Entity wcb)) ])) 
	= bind(pushSubsts(idS)(mapper, wcb), SubstsT[Entity] (Entity _) { return boundSu(mapper, wcb); });
public SubstsT[Entity] boundSu(Mapper mapper, entity([ *ids, wildcard(super(Entity wcb)) ])) = lift(tzero());

public SubstsT[Entity] boundSu(Mapper mapper, entity([ *ids, captureof(Entity wcd) ])) = boundSu(mapper, wcd); // captures

public default SubstsT[Entity] boundSu(Mapper mapper, Entity v) = returnS(v);

@doc{The upper bind semantics that introduces new type argument variables but does not bind type argument variables}
public SubstsT[Entity] boundSu_(Mapper mapper, tp:entity([ *ids, typeParameter(str _)]))
	= bind(popSubsts(), SubstsT[Entity] (Substs s) {
			Entity b = lookupSubsts(s, tp);
			if(b == tp) return returnS(tp);
			return bind(pushSubsts(idS)(mapper, b), SubstsT[Entity] (Entity b_) { 
						return boundSu_(mapper, b_); });
			});
public SubstsT[Entity] boundSu_(Mapper mapper, entity([ *ids, ta:typeArgument(str _, _, entity([ *ids, wildcard() ]))])) // case of 'Ta'
	= boundSu_(mapper, entity( ids + ta + upper(zero()) ));
public SubstsT[Entity] boundSu_(Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, entity([ *ids, wildcard(extends(Entity wcb)) ]))])) // case of 'Ta'
	= boundSu_(mapper, entity( ids + ta + upper(wcb) ));
public SubstsT[Entity] boundSu_(Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, entity([ *ids, wildcard(super(Entity wcb)) ]))])) // case of 'Ta'
	= boundSu_(mapper, entity( ids + ta + upper(zero()) ));
public SubstsT[Entity] boundSu_(Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, Entity init)])) // case of 'Ta'
	= boundSu_(mapper, entity( ids + ta + upper(init)));

public SubstsT[Entity] boundSu_(Mapper mapper, entity([])) = lift(tzero());
public SubstsT[Entity] boundSu_(Mapper mapper, entity([ *ids, wildcard() ])) = lift(tzero());
public SubstsT[Entity] boundSu_(Mapper mapper, entity([ *ids, wildcard(extends(Entity wcb)) ])) 
	= bind(pushSubsts(idS)(mapper, wcb), SubstsT[Entity] (Entity _) { return boundSu_(mapper, wcb); });
public SubstsT[Entity] boundSu_(Mapper mapper, entity([ *ids, wildcard(super(Entity wcb)) ])) = lift(tzero());

public SubstsT[Entity] boundSu_(Mapper mapper, entity([ *ids, captureof(Entity wcd) ])) = boundSu_(mapper, wcd); // captures

public default SubstsT[Entity] boundSu_(Mapper mapper, Entity v) = returnS(v);
	
@doc{The lower bind semantics that introduces new type argument variables and uses the extended bind semantics}
public SubstsT[Entity] boundSl(Mapper mapper, tp:entity([ *ids, typeParameter(str _)]))
	= bind(popSubsts(), SubstsT[Entity] (Substs s) {
			Entity b = lookupSubsts(s, tp);
			if(b == tp) return returnS(tp);
			return bind(pushSubsts(idS)(mapper, b), SubstsT[Entity] (Entity b_) { 
						return boundSl(mapper, b_); });
			});
public SubstsT[Entity] boundSl(Mapper mapper, entity([ *ids, ta:typeArgument(str _, _, entity([ *ids, wildcard() ]))])) // case of 'Ta'
	= boundSl(mapper, entity( ids + ta + lower(zero()) ));
public SubstsT[Entity] boundSl(Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, entity([ *ids, wildcard(extends(Entity wcb)) ]))])) // case of 'Ta'
	= boundSl(mapper, entity( ids + ta + lower(zero()) ));
public SubstsT[Entity] boundSl(Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, entity([ *ids, wildcard(super(Entity wcb)) ]))])) // case of 'Ta'
	= boundSl(mapper, entity( ids + ta + lower(wcb) ));
public SubstsT[Entity] boundSl(Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, Entity init)])) // case of 'Ta'
	= boundSl(mapper, entity( ids + ta + lower(init)));

public SubstsT[Entity] boundSl(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(Entity _)])) // case of 'Ta_l'
	= boundS(mapper, ta);
public SubstsT[Entity] boundSl(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(Entity _)])) // case of 'Ta_u'
	= boundS(mapper, ta);

public SubstsT[Entity] boundSl(Mapper mapper, entity([])) = lift(tzero());
public SubstsT[Entity] boundSl(Mapper mapper, entity([ *ids, wildcard() ])) = lift(tzero());
public SubstsT[Entity] boundSl(Mapper mapper, entity([ *ids, wildcard(extends(Entity wcb)) ])) = lift(tzero());
public SubstsT[Entity] boundSl(Mapper mapper, entity([ *ids, wildcard(super(Entity wcb)) ])) 
	= bind(pushSubsts(idS)(mapper, wcb), SubstsT[Entity] (Entity _) { return boundSl(mapper, wcb); });
	
public SubstsT[Entity] boundSl(Mapper mapper, entity([ *ids, captureof(Entity wcd) ])) = boundSl(mapper, wcd); // captures
	
public default SubstsT[Entity] boundSl(Mapper mapper, Entity v) = returnS(v);

@doc{The lower bind semantics that introduces new type argument variables but does not bind type argument variables}
public SubstsT[Entity] boundSl_(Mapper mapper, tp:entity([ *ids, typeParameter(str _)]))
	= bind(popSubsts(), SubstsT[Entity] (Substs s) {
			Entity b = lookupSubsts(s, tp);
			if(b == tp) return returnS(tp);
			return bind(pushSubsts(idS)(mapper, b), SubstsT[Entity] (Entity b_) { 
						return boundSl_(mapper, b_); });
			});
public SubstsT[Entity] boundSl_(Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, entity([ *ids, wildcard() ]))])) // case of 'Ta'
	= boundSl_(mapper, entity( ids + ta + lower(zero()) ));
public SubstsT[Entity] boundSl_(Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, entity([ *ids, wildcard(extends(Entity wcb)) ]))])) // case of 'Ta'
	= boundSl_(mapper, entity( ids + ta + lower(zero()) ));
public SubstsT[Entity] boundSl_(Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, entity([ *ids, wildcard(super(Entity wcb)) ]))])) // case of 'Ta'
	= boundSl_(mapper, entity( ids + ta + lower(wcb) ));
public SubstsT[Entity] boundSl_(Mapper mapper, entity([ *ids, ta:typeArgument(str _,_, Entity init)])) // case of 'Ta'
	= boundSl_(mapper, entity( ids + ta + lower(init)));

public SubstsT[Entity] boundSl_(Mapper mapper, entity([])) = lift(tzero());
public SubstsT[Entity] boundSl_(Mapper mapper, entity([ *ids, wildcard() ])) = lift(tzero());
public SubstsT[Entity] boundSl_(Mapper mapper, entity([ *ids, wildcard(extends(Entity wcb)) ])) = lift(tzero());
public SubstsT[Entity] boundSl_(Mapper mapper, entity([ *ids, wildcard(super(Entity wcb)) ])) 
	= bind(pushSubsts(idS)(mapper, wcb), SubstsT[Entity] (Entity _) { return boundSl_(mapper, wcb); });
	
public SubstsT[Entity] boundSl_(Mapper mapper, entity([ *ids, captureof(Entity wcd) ])) = boundSl_(mapper, wcd); // captures
	
public default SubstsT[Entity] boundSl_(Mapper mapper, Entity v) = returnS(v);

