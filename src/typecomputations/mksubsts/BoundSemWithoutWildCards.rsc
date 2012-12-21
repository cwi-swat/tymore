module typecomputations::mksubsts::BoundSemWithoutWildCards

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;
import lang::java::jdt::refactorings::PrettyPrintUtil;
import lang::java::jdt::refactorings::ValuesUtil;

import typecomputations::mksubsts::BoundSemWithWildCards;
import typecomputations::mksubsts::LanguageInterface;
import typecomputations::mksubsts::SubstitutionMonad;
import typecomputations::mksubsts::TypeValuesFuncs;

import IO;
import List;
import Map;
import Set;

public Entity lookupSubsts(Substs s, Entity v) {
	map[Entity, Entity] mapOfs = ();
	if(!isEmpty(s.params))
		for(int i <- [0..size(s.params) - 1])
			mapOfs[s.params[i]] = s.args[i];
	return mapOfs[v] ? zero();
}

public Entity lookupEnv(CompilUnit facts, Entity v) {
	list[Entity] boundsOftp = typeParamBounds(facts, v);
	map[Entity, Entity] mapOfs = ();
	for(Entity tpb <- boundsOftp) mapOfs[v] = tpb;
	if(isEmpty(mapOfs)) mapOfs[v] = object();
	return mapOfs[v];
}

public SubstsT[Entity] boundEnv(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str name)]))
	= bind(pushSubsts(paramSubstsWith(mapper, tp))(mapper, lookupEnv(facts, tp)), SubstsT[Entity] (Entity b) {
			return boundEnv(facts, mapper, b); }); 	
public default SubstsT[Entity] boundEnv(CompilUnit facts, Mapper mapper, Entity v) = returnS(v);

public SubstsT[Entity] boundS(Mapper mapper, tp:entity([ *ids, typeParameter(str _)]))
	= bind(popSubsts(), SubstsT[Entity] (Substs s) {
			Entity b = lookupSubsts(s, tp);
			if(b == tp) return returnS(tp);
			return bind(pushSubsts(idS)(mapper, b), SubstsT[Entity] (Entity b_) { 
						return boundS(mapper, b_); });
			});
public SubstsT[Entity] boundS(Mapper mapper, entity([])) = lift(tzero());
public SubstsT[Entity] boundS(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, entity([]))])) // case of 'Ta'
	= lift(tzero());
public SubstsT[Entity] boundS(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity initv)])) // case of 'Ta'
	= pushSubsts(paramSubstsWith(mapper, ta))(mapper, initv);

// extends to account for wildcards
public SubstsT[Entity] boundS(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(entity([]))]))
	= lift(tzero());
public SubstsT[Entity] boundS(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(Entity init)]))
	= boundSu(mapper, ta);
	
public SubstsT[Entity] boundS(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(entity([]))]))
	= lift(tzero());
public SubstsT[Entity] boundS(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(Entity init)]))
	= boundSl(mapper, ta);

public default SubstsT[Entity] boundS(Mapper mapper, Entity v) = returnS(v);

// no cases of Ta
public SubstsT[Entity] boundS_(Mapper mapper, tp:entity([ *ids, typeParameter(str _)]))
	= bind(popSubsts(), SubstsT[Entity] (Substs s) {
			Entity b = lookupSubsts(s, tp);
			if(b == tp) return returnS(tp);
			return bind(pushSubsts(idS)(mapper, b), SubstsT[Entity] (Entity b_) { 
						return boundS_(mapper, b_); });
			});
public default SubstsT[Entity] boundS_(Mapper mapper, Entity v) = returnS(v);
