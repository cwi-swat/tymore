@license{
  Copyright (c) 2009-2012 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - A.Izmaylova@cwi.nl}
module prototype::computations::mksubsts::FunctionsOfTypeValues

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import prototype::lang::java::jdt::refactorings::Java;
import prototype::lang::java::jdt::refactorings::JavaADT;
import prototype::lang::java::jdt::refactorings::PrettyPrintUtil;
import prototype::lang::java::jdt::refactorings::ValuesUtil;

import prototype::computations::mksubsts::LanguageInterface;

import IO;
import List;
import Map;
import Set;

@doc{Evaluation function: evaluates a declaration type value to the associated declared type}	
public Entity eval(entity([ *ids, constr(_) ])) = entity(ids);		
public Entity eval(entity([ *ids, constr(_,_) ])) = entity(ids);
public Entity eval(entity([ *_, method(_,_, Entity declaredType) ])) = declaredType;
public Entity eval(entity([ *_, method(_,_,_, Entity declaredType) ])) = declaredType;
public Entity eval(entity([ *_, enumConstant(_, Entity declaredType) ])) = declaredType;
public Entity eval(entity([ *_, field(_, Entity declaredType) ])) = declaredType;
public Entity eval(entity([ *_, \parameter(_, Entity declaredType) ])) = declaredType;
public Entity eval(entity([ *_, variable(_, Entity declaredType, _) ])) = declaredType;
public Entity eval(entity([ *_, anonymous(_, Entity declaredType) ])) = declaredType;
public Entity eval(entity([ *_, inherits(Entity declaredType) ])) = declaredType;
/* Note: 
* 	in case of constructors, i.e. new A().new B(), the declaring type is evaluated to the type that declares the type, 
*   objects of which the constructor creates */ 
public Entity eval(entity([ *ids, constr(_), decl() ])) = eval(entity(ids + decl()));
public Entity eval(entity([ *ids, constr(_,_), decl() ])) = eval(entity(ids + decl()));
public Entity eval(entity([ *ids, id, decl() ])) = entity(ids);
public Entity eval(entity([ *_, constr(list[Entity] params), \parameter(int i) ])) = params[i];
public Entity eval(entity([ *_, method(_, list[Entity] params, _), \parameter(int i) ])) = params[i];
public Entity eval(entity([ *_, constr(_, list[Entity] params), \parameter(int i) ])) = params[i];
public Entity eval(entity([ *_, method(_,_, list[Entity] params,_), \parameter(int i) ])) = params[i];
public default Entity eval(Entity val) = val;

@doc{Declaring types}
public Entity decl(Entity val) = entity(val.id + decl());
@doc{Declared parameter types}
public Entity (Entity) param(int i) = Entity (Entity val) { return entity(val.id + \parameter(i)); };
@doc{Declared inheritance relation}
public Entity inherits(Entity t1, Entity t2) = entity(t1.id + inherits(t2));

public map[Entity, PEntity] memoMkSubsts = ();
@doc{Makes the semantics with the explicit substitutions of type parameters}
public PEntity mkSubsts(CompilUnit facts, Mapper mapper, Entity v) 
	= memoMkSubsts[v] ? { PEntity pv = toGensNonRec(facts, mapper)(v); memoMkSubsts[v] = pv; return pv; };

@doc{Gets the generic part of a parameterized type}
public Entity getGenV(PEntity v) = v.genval;
public Entity getGenV(CompilUnit facts, Mapper mapper, Entity v) = mkSubsts(facts, mapper, v).genval;

public Substs getSubsts(PEntity v) = v.s;
public Substs getSubsts(CompilUnit facts, Mapper mapper, Entity v) = mkSubsts(facts, mapper, v).s;

@doc{Parameterizes the type argument part of explicit substitution with some context}
public Substs (Substs) paramSubstsWith(CompilUnit facts, Mapper mapper, &C c) 
	= Substs (Substs s) {
		if(size(s.params) == size(s.args) && isEmpty(s.params)) return s;
		list[Entity] pargs = [ typeArgument(facts, mapper, s.params[i], s.args[i], c) | int i <- [0..size(s.params)] ];
		return substs(pargs, s.params);
	};
	
@doc{Cases of type parameters as inits}
public Entity typeArgument(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str name) ]), init:entity([ *ids, typeParameter(_) ]), &C c) 
	= init;
public Entity typeArgument(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str name) ]), init:entity([ *ids, typeParameter(_,_) ]), &C c) 
	= init;
public default Entity typeArgument(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str name) ]), Entity init, &C c)
	 = !hasRawTypeArgument(facts, mapper, init) ? init : entity([ typeArgument(name, c, init) ]);

private bool hasRawTypeArgument(CompilUnit facts, Mapper mapper, entity([])) = true;
private default bool hasRawTypeArgument(CompilUnit facts, Mapper mapper, Entity init) {
	PEntity pinit = mkSubsts(facts, mapper, init);
	if(Entity arg <- pinit.s.args, arg == zero() || hasRawTypeArgument(facts, mapper, arg)) return true;
	return false;
}

public PEntity (Entity) toGensNonRec(CompilUnit facts, Mapper mapper) 
	= PEntity (Entity val) { 
		return toGensNonRecByCase(facts, mapper, val); 
	};
	
public PEntity toGensNonRecByCase(CompilUnit facts, Mapper mapper, val:entity([])) = pzero()[@paramval=val];
public PEntity toGensNonRecByCase(CompilUnit facts, Mapper mapper, val:entity([ *ids, anonymous(_,_)])) = pentity(substs([],[]), val)[@paramval=val];
public PEntity toGensNonRecByCase(CompilUnit facts, Mapper mapper, val:entity([ *ids, decl() ])) {
	PEntity pval = toGensNonRec(facts, mapper)(entity(ids));
	return pentity(pval.s, decl(pval.genval))[@paramval = val];
}
public PEntity toGensNonRecByCase(CompilUnit facts, Mapper mapper, val:entity([ *ids, \parameter(int i) ])) {
	PEntity pval = toGensNonRec(facts, mapper)(entity(ids));
	return pentity(pval.s, param(i)(pval.genval))[@paramval = val];
}
public default PEntity toGensNonRecByCase(CompilUnit facts, Mapper mapper, Entity val) {
	if(isTypeParameter(val) || isWildCardType(val) || isTypeArgument(val)) 
		return pentity(substs([],[]), val)[@paramval=val];
	
	Substitutions val_ = mapper[val];
	Entity genval = val_.val; 
	list[Entity] args = val_.substs.targs; 
	list[Entity] params = val_.substs.tparams;	
	
	// special treatment of static members
	if(isStatic(facts, val) && Entity d := getDeclaringType(val) && d != zero()) {
		// DEBUG static entities:
		println("STATIC value : <prettyprint(val)>; <prettyprint(d)>; [ <for(p<-params){><prettyprint(p)>; <}> ]");
		Substs ds = getSubsts(facts, mapper, d);
		println("Substitution: <prettyprint(ds)>");
		list[int] paramsOut = []; // increasing indices
		if(ds != substs([],[]) && !isEmpty(params)) {
			for(int i <- [0..size(params)]) {
				if(params[i] in ds.params)
					paramsOut = paramsOut + [i];
			}
		}
		for(int indx <- reverse(paramsOut)) { // removing in reverse order
			args = delete(args, indx);
			params = delete(params, indx);
		}
	}
	
	assert(size(args)==size(params));
		
	if(isEmpty(params)) return pentity(substs([],[]), genval)[@paramval=val];
	list[Entity] pargs = [ (entity([]) := args[i]) ? zero() : args[i] | int i <- [0..size(params)] ];
	PEntity res = pentity(substs(pargs, params), genval)[@paramval=val];
	// DEBUG entities:
	if(isStatic(facts, val) && Entity d := getDeclaringType(val) && d != zero()) println(prettyprint(res));
	return res;
}

public Substs idS(Substs s) = s;

@doc{EXTENSION with wildcards: extends to account for wildcards ***with capturing***}
public Entity typeArgument(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str name) ]), init:entity([]), &C c) 
	= entity([ captureof(entity([ typeArgument(name, c, init) ])) ]);
public Entity typeArgument(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str name) ]), init:entity([ *_, wildcard() ]), &C c) 
	= entity([ captureof(entity([ typeArgument(name, c, init) ])) ]);
public Entity typeArgument(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str name) ]), init:entity([ *_, wildcard(_) ]), &C c)
	= entity([ captureof(entity([ typeArgument(name, c, init) ])) ]);	
// !!! TODO: re-think of this case
//public Entity typeArgument(Mapper mapper, tp:entity([ *ids, typeParameter(str name) ]), init:entity([ *_, captureof(_) ]), &C c)
//	= entity([ captureof(entity([ typeArgument(name, c, init) ])) ]);

@doc{EXTENSION with wildcards: extends to account for wildcards ***without capturing***}
public Entity typeArgumentNoCapture(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str name) ]), init:entity([]), &C c) 
	= entity([ typeArgument(name, c, init) ]);
public Entity typeArgumentNoCapture(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str name) ]), init:entity([ *_, wildcard() ]), &C c) 
	= entity([ typeArgument(name, c, init) ]);
public Entity typeArgumentNoCapture(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str name) ]), init:entity([ *_, wildcard(_) ]), &C c)
	= entity([ typeArgument(name, c, init) ]);
public default Entity typeArgumentNoCapture(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str name) ]), Entity init, &C c)
	= typeArgument(facts, mapper, tp, init, c);	

@doc{EXTENSION with wildcards: parameterizes the type argument part of explicit substitution with some context - ***without capturing***}
public Substs (Substs) paramSubstsWithNoCapture(CompilUnit facts, Mapper mapper, &C c) 
	= Substs (Substs s) {
		if(size(s.params) == size(s.args) && isEmpty(s.params)) return s;
		list[Entity] pargs = [ typeArgumentNoCapture(facts, mapper, s.params[i], s.args[i], c) | int i <- [0..size(s.params)] ];
		return substs(pargs, s.params);
	};

@doc{EXTENSION with wildcards}
private bool hasRawTypeArgument(CompilUnit facts, Mapper mapper, init:entity([ *_, wildcard() ])) = false;
private bool hasRawTypeArgument(CompilUnit facts, Mapper mapper, init:entity([ *_, wildcard(_) ])) {
	PEntity pinit = mkSubsts(facts, mapper, boundWildcard(init));
	if(Entity arg <- pinit.s.args, arg == zero() || hasRawTypeArgument(facts, mapper, arg)) return true;
	return false;
}
// !!! TODO: re-think of this case 
//private bool hasRawTypeArgument(CompilUnit facts, Mapper mapper, init:entity([ *_, captureof(_) ])) {
//	PEntity pinit = mkSubsts(facts, mapper, boundWildcardUB(init));
//	if(Entity arg <- pinit.s.args, arg == zero() || hasRawTypeArgument(facts, mapper, arg)) return true;
//	return false;
//}
