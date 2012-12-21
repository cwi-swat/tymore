module typecomputations::mksubsts::BoundSemWithWildCards

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;
import lang::java::jdt::refactorings::PrettyPrintUtil;
import lang::java::jdt::refactorings::ValuesUtil;

import typecomputations::mksubsts::BoundSemWithoutWildCards;
import typecomputations::mksubsts::LanguageInterface;
import typecomputations::mksubsts::SubstitutionMonad;
import typecomputations::mksubsts::TypeComputation;
import typecomputations::mksubsts::TypeValuesFuncs;


import IO;
import List;
import Map;
import Set;

// ===== bound _ S ^ u

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

public SubstsT[Entity] boundSu(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(entity([]))])) // case of 'Ta_u'
	= lift(tzero());
public SubstsT[Entity] boundSu(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(Entity init)])) // case of 'Ta_u'
	= pushSubsts(paramSubstsWith(mapper, ta))(mapper, init);
public SubstsT[Entity] boundSu(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(entity([]))])) // case of 'Ta_u'
	= lift(tzero());
public SubstsT[Entity] boundSu(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(Entity init)])) // case of 'Ta_u'
	= pushSubsts(paramSubstsWith(mapper, ta))(mapper, init);

public SubstsT[Entity] boundSu(Mapper mapper, entity([])) = lift(tzero());
public SubstsT[Entity] boundSu(Mapper mapper, entity([ *ids, wildcard() ])) = lift(tzero());
public SubstsT[Entity] boundSu(Mapper mapper, entity([ *ids, wildcard(extends(Entity wcb)) ])) 
	= bind(pushSubsts(idS)(mapper, wcb), SubstsT[Entity] (Entity _) { return boundSu(mapper, wcb); });
public SubstsT[Entity] boundSu(Mapper mapper, entity([ *ids, wildcard(super(Entity wcb)) ])) = lift(tzero());

public SubstsT[Entity] boundSu(Mapper mapper, entity([ *ids, captureof(Entity wcd) ])) = boundSu(mapper, wcd); // captures

public default SubstsT[Entity] boundSu(Mapper mapper, Entity v) = returnS(v);

// ===== bound _ S ^ u - A

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
	
// ===== bound _ S ^ l

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

public SubstsT[Entity] boundSl(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(entity([]))])) // case of 'Ta_l'
	= lift(tzero());
public SubstsT[Entity] boundSl(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), lower(Entity init)])) // case of 'Ta_l'
	= pushSubsts(paramSubstsWith(mapper, ta))(mapper, init);
public SubstsT[Entity] boundSl(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(entity([]))])) // case of 'Ta_l'
	= lift(tzero());
public SubstsT[Entity] boundSl(Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, Entity _), upper(Entity init)])) // case of 'Ta_l'
	= pushSubsts(paramSubstsWith(mapper, ta))(mapper, init);

public SubstsT[Entity] boundSl(Mapper mapper, entity([])) = lift(tzero());
public SubstsT[Entity] boundSl(Mapper mapper, entity([ *ids, wildcard() ])) = lift(tzero());
public SubstsT[Entity] boundSl(Mapper mapper, entity([ *ids, wildcard(extends(Entity wcb)) ])) = lift(tzero());
public SubstsT[Entity] boundSl(Mapper mapper, entity([ *ids, wildcard(super(Entity wcb)) ])) 
	= bind(pushSubsts(idS)(mapper, wcb), SubstsT[Entity] (Entity _) { return boundSl(mapper, wcb); });
	
public SubstsT[Entity] boundSl(Mapper mapper, entity([ *ids, captureof(Entity wcd) ])) = boundSl(mapper, wcd); // captures
	
public default SubstsT[Entity] boundSl(Mapper mapper, Entity v) = returnS(v);

// =====

public SubstsT[Entity] boundSl_(Mapper mapper, tp:entity([ *ids, typeParameter(str _)]))
	= bind(popSubsts(), SubstsT[Entity] (Substs s) {
			Entity b = lookupSubsts(s, tp);
			if(b == tp) return returnS(tp);
			return bind(pushSubsts(idS)(mapper, b), SubstsT[Entity] (Entity b_) { 
						return boundSl_(mapper, b_); });
			});
public SubstsT[Entity] boundSl_(Mapper mapper, entity([ *ids, ta:typeArgument(str _, _, entity([ *ids, wildcard() ]))])) // case of 'Ta'
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


// =====

public Entity getUpperB(ta:entity([ *ids, typeArgument(_,_,_), upper(_) ])) = ta;
public Entity getUpperB(ta:entity([ *ids, typeArgument(_,_,_), lower(_) ])) = ta;

public Entity getUpperB(entity([ *ids, captureof(Entity ta) ])) = getUpperB(ta);

public Entity getUpperB(ta:entity([ *ids, typeArgument(_,_,entity([ *ids, wildcard() ])) ])) = entity(ta.id + upper(zero()));
public Entity getUpperB(ta:entity([ *ids, typeArgument(_,_,entity([ *ids, wildcard(extends(Entity wcb)) ])) ])) = entity(ta.id + upper(wcb));
public Entity getUpperB(ta:entity([ *ids, typeArgument(_,_,entity([ *ids, wildcard(super(Entity wcb)) ])) ])) = entity(ta.id + upper(zero()));

public default Entity getUpperB(Entity v) = boundWcardUB(v);

public Entity getLowerB(ta:entity([ *ids, typeArgument(_,_,_), upper(_) ])) = ta;
public Entity getLowerB(ta:entity([ *ids, typeArgument(_,_,_), lower(_) ])) = ta;

public Entity getLowerB(entity([ *ids, captureof(Entity ta) ])) = getLowerB(ta);

public Entity getLowerB(ta:entity([ *ids, typeArgument(_,_,entity([ *ids, wildcard() ])) ])) = entity(ta.id + lower(zero()));
public Entity getLowerB(ta:entity([ *ids, typeArgument(_,_,entity([ *ids, wildcard(extends(Entity wcb)) ])) ])) = entity(ta.id + lower(zero()));
public Entity getLowerB(ta:entity([ *ids, typeArgument(_,_,entity([ *ids, wildcard(super(Entity wcb)) ])) ])) = entity(ta.id + lower(wcb));

public default Entity getLowerB(Entity v) = boundWcardLB(v);

