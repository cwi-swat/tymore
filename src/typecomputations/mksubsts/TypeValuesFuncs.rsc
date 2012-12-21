module typecomputations::mksubsts::TypeValuesFuncs

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;
import lang::java::jdt::refactorings::PrettyPrintUtil;
import lang::java::jdt::refactorings::ValuesUtil;

import IO;
import List;
import Map;
import Set;


public map[Entity, PEntity] memoMkSubsts = ();
@doc{Makes the semantics with the explicit substitutions of type parameters}
public PEntity mkSubsts(Mapper mapper, Entity v) 
	= memoMkSubsts[v] ? { PEntity pv = toGensNonRec(mapper)(v); memoMkSubsts[v] = pv; return pv; };

public PEntity (Entity) toGensNonRec(Mapper mapper) 
	= PEntity (Entity v) { 
		if(v == zero()) return pentity(substs([],[]), zero())[@paramval=zero()]; 
		if(isTypeParameter(v) || isWildCardType(v) || isTypeArgument(v)) return pentity(substs([],[]), v)[@paramval=v];
		if(entity([ *ids, anonymous(_,_)]) := v) return pentity(substs([],[]), v)[@paramval=v];
		if(entity([ *ids, decl() ]) := v) {
			PEntity pv = toGensNonRec(mapper)(entity(ids));
			return pentity(pv.s, decl(pv.genval))[@paramval = v];
		}
		if(entity([ *ids, \parameter(int i) ]) := v) {
			PEntity pv = toGensNonRec(mapper)(entity(ids));
			return pentity(pv.s, param(i)(pv.genval))[@paramval = v];
		}
		tuple[tuple[list[Entity], list[Entity]], Entity] v_ = mapper[v];
		Entity genval = v_[1]; 
		list[Entity] args = v_[0][0]; 
		list[Entity] params = v_[0][1];	
		
		assert(size(args)==size(params)); // assertion
		
		if(isEmpty(params)) return pentity(substs([], []), genval)[@paramval=v];
		list[Entity] pargs = [ (entity([]) := args[i]) ? zero() : args[i] | int i <- [0..(size(params) - 1)] ];
		return pentity(substs(pargs, params), genval)[@paramval=v]; 
	};
	
@doc{Gets the generic part of a parameterized type}
public Entity getGenV(PEntity v) = v.genval;
public Entity getGenV(Mapper mapper, Entity v) = mkSubsts(mapper, v).genval;

public Substs getSubsts(PEntity v) = v.s;
public Substs getSubsts(Mapper mapper, Entity v) = mkSubsts(mapper, v).s;

@doc{Parameterizes the type argument part of explicit substitution with some context}
public Substs (Substs) paramSubstsWith(Mapper mapper, &C c) 
	= Substs (Substs s) {
		if(size(s.params) == size(s.args) && isEmpty(s.params)) return s;
		list[Entity] pargs = [ typeArgument(mapper, s.params[i], s.args[i], c) | int i <- [0..size(s.params) - 1] ];
		return substs(pargs, s.params);
	};

public Substs (Substs) paramSubstsWithCapture(Mapper mapper, &C c) 
	= Substs (Substs s) {
		if(size(s.params) == size(s.args) && isEmpty(s.params)) return s;
		list[Entity] pargs = [ typeArgumentCapture(mapper, s.params[i], s.args[i], c) | int i <- [0..size(s.params) - 1] ];
		return substs(pargs, s.params);
	};
	
public Entity typeArgumentCapture(Mapper mapper, tp:entity([ *ids, typeParameter(str name) ]), Entity init, &C c)
	 = ( (isTypeParameter(init) || !hasRawTypeArgument(mapper, init)) && !isWildCardType(init) ) ? init 
	 	: entity([ captureof(entity([ typeArgument(name, c, init) ])) ]) ;

	
public Substs idS(Substs s) = s;
	
public Entity typeArgument(Mapper mapper, tp:entity([ *ids, typeParameter(str name) ]), Entity init, &C c)
	 = ( isTypeParameter(init) || !hasRawTypeArgument(mapper, init) ) ? init : entity([ typeArgument(name, c, init) ]);

private bool hasRawTypeArgument(Mapper mapper, Entity init) {
	if(init == zero()) return true;
	PEntity pinit = mkSubsts(mapper, init);
	if(isWildCardType(init)) pinit = mkSubsts(mapper, boundWcardUB(init));
	if(Entity arg <- pinit.s.args, arg == zero() || hasRawTypeArgument(mapper, arg)) return true;
	return false;
}



