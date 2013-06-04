@license{
  Copyright (c) 2009-2011 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - A.Izmaylova@cwi.nl}
module prototype::lang::java::jdt::refactorings::ValuesUtil

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import prototype::lang::java::jdt::refactorings::Java;
import prototype::lang::java::jdt::refactorings::JavaADT;

import List;
import IO;

@doc{Returns true if an anonymous declared type}
public bool isAnonymous(Entity val) = (entity([ *ids, anonymous(loc _, Entity _) ]) := val);
@doc{Returns true if a binding to an array type}
public bool isArrayType(Entity val) = (entity([ *ids, array(Entity _) ]) := val);
@doc{Returns true if a method binding}
public bool isMethodBinding(Entity val) = ( (entity([ *_, method(_,_,_) ]) := val) || (entity([ *_, method(_,_,_,_) ]) := val) );
@doc{Returns true if the method binding is a constructor binding}
public bool isConstructorBinding(Entity val) = ( (entity([ *_, constr(_) ]) := val) || (entity([ *_, constr(_,_) ]) := val));
@doc{Returns true if a variable binding (fields, formal parameters, local variables)}							 
public bool isVariableBinding(Entity val) = ( (entity([ *_, enumConstant(_,_) ]) := val) 
											|| (entity([ *_, field(_,_) ]) := val) 
											|| (entity([ *_, \parameter(_,_) ]) := val) 
											|| (entity([ *_, variable(_,_,_) ]) := val)
											|| (entity([ *_, \parameter(_) ]) := val) );
@doc{Returns true if a variable binding to a field}							 
public bool isFieldBinding(Entity val) = (entity([ *ids, field(_,_) ]) := val);
@doc{Returns true if a type parameter}
public bool isTypeParameter(Entity val) = ( entity([ *ids, typeParameter(_) ]) := val || entity([ *ids, typeParameter(_,_) ]) := val );
@doc{Returns true if a type binding (classes, interfaces, primitive types, type parameters)}
public bool isType(Entity val) = (  (entity([ *_, class(_) ]) := val) 
								 || (entity([ *_, class(_,_) ]) := val) 
								 || (entity([ *_, interface(_) ]) := val) 
								 || (entity([ *_, interface(_,_) ]) := val)
								 || (entity([ *_, anonymousClass(_)]) := val) 
								 || (entity([ *_, enum(_) ]) := val)
								 || (entity([ *_, primitive(_) ]) := val)
								 || (entity([ *_, array(_) ]) := val)
								 || (entity([ *_, typeParameter(_,_) ]) := val)
								 || (entity([ *_, wildcard() ]) := val)
								 || (entity([ *_, wildcard(_) ]) := val)
								 || (entity([ *_, captureof(_) ]) := val) );
@doc{Returns true if a type binding is an array or primitive type}
public bool isArrayOrPrimitiveType(Entity val) = (  (entity([ *_, primitive(_) ]) := val)
								 || (entity([ *_, array(_) ]) := val) );
@doc{Returns true if a wildcard binding}									
public bool isWildCardType(Entity val) = (  (entity([ *_, wildcard() ]) := val)
										 || (entity([ *_, wildcard(_) ]) := val)
										 || (entity([ *_, captureof(_) ]) := val) );

@doc{Returns type parameters or type arguments of methods,	
	 Note: the constructor type values are treated separately, i.e. type parameters (type arguments) of the declaring type are taken into account}									 
public list[Entity] getGenericTypes(entity([ *ids, class(_, list[Entity] params), constr(_) ])) = params;
public list[Entity] getGenericTypes(entity([ *ids, class(_), constr(list[Entity] genericTypes,_) ])) = genericTypes;
public list[Entity] getGenericTypes(entity([ *ids, class(_, list[Entity] params), constr(list[Entity] genericTypes,_) ])) = params + genericTypes;
public list[Entity] getGenericTypes(entity([ *_, method(list[Entity] genericTypes,_,_,_) ])) = genericTypes;
public default list[Entity] getGenericTypes(Entity val) = [];
@doc{Returns the type parameters of a generic type or type arguments of a parameterized type}
public list[Entity] getTypeParamsOrArgs(entity([ *ids, class(_, list[Entity] params) ])) = getTypeParamsOrArgs(entity(ids)) + params;
public list[Entity] getTypeParamsOrArgs(entity([ *ids, interface(_, list[Entity] params) ])) = getTypeParamsOrArgs(entity(ids)) + params;
public default list[Entity] getTypeParamsOrArgs(Entity val) = [];
@doc{Returns true if a type parameter}
public bool isTypeParameter(PEntity val) = isTypeParameter(val.genval);
@doc{Returns true if a type argument value}
public bool isTypeArgument(entity([ *ids, typeArgument(str name, _, Entity _) ])) = true;
@doc{EXTENSION with wildcards}
public bool isTypeArgument(entity([ *ids, typeArgument(str name, _, Entity _), upper(_) ])) = true;
public bool isTypeArgument(entity([ *ids, typeArgument(str name, _, Entity _), lower(_) ])) = true;
public default bool isTypeArgument(_) = false;

@doc{EXTENSION with wildcards}
public bool isLowerBoundTypeArgument(entity([ *ids, typeArgument(str name, _, Entity _), lower(_) ])) = true;
public default bool isLowerBoundTypeArgument(Entity _) = false;
public bool isUpperBoundTypeArgument(entity([ *ids, typeArgument(str name, _, Entity _), upper(_) ])) = true;
public default bool isUpperBoundTypeArgument(Entity _) = false;

@doc{EXTENSION with wildcards}
public Entity replaceWithUpper(entity([ *ids, ta:typeArgument(str name, _, Entity _), lower(Entity b) ]))
	= entity([ *ids, ta, upper(b) ]);
public default Entity replaceWithUpper(Entity val) = val;
public Entity replaceWithLower(entity([ *ids, ta:typeArgument(str name, _, Entity _), upper(Entity b) ]))
	= entity([ *ids, ta, lower(b) ]);
public default Entity replaceWithLower(Entity val) = val;


public bool isCapturedTypeArgument(entity([ *ids, captureof(Entity v) ])) = isTypeArgument(v);
public default bool isCapturedTypeArgument(Entity _) = false;

public Entity getTypeParameter(entity([ *ids, typeArgument(str name, _,_) ])) = entity([typeParameter(name)]);
@doc{EXTENSION with wildcards}
public Entity getTypeParameter(entity([ *ids, typeArgument(str name, _,_), upper() ])) = entity([typeParameter(name)]);
public Entity getTypeParameter(entity([ *ids, typeArgument(str name, _,_), lower() ])) = entity([typeParameter(name)]);

public Entity getInit(entity([ *ids, typeArgument(str name, _, Entity init) ])) = init;
public default Entity getInit(_) = zero();
@doc{EXTENSION with wildcards}
public Entity getInit(entity([ *ids, typeArgument(str name, _, Entity _), upper(Entity init) ])) = init;
public Entity getInit(entity([ *ids, typeArgument(str name, _, Entity _), lower(Entity init) ])) = init;

@doc{EXTENSION with wildcards}
public Entity boundWildcardUB(entity([ *ids, wildcard() ])) = zero();
public Entity boundWildcardUB(entity([ *ids, wildcard(extends(Entity wcb)) ])) = wcb;
public Entity boundWildcardUB(entity([ *ids, captureof(wildcard(extends(Entity wcb))) ])) = wcb;
public Entity boundWildcardUB(entity([ *ids, wildcard(super(Entity wcb)) ])) = zero();
public Entity boundWildcardUB(entity([ *ids, captureof(wildcard(super(Entity wcb))) ])) = zero();
public default Entity boundWildcardUB(Entity val) = val;
@doc{EXTENSION with wildcards}
public Entity boundWildcardLB(entity([ *ids, wildcard() ])) = zero();
public Entity boundWildcardLB(entity([ *ids, wildcard(super(Entity wcb)) ])) = wcb;
public Entity boundWildcardLB(entity([ *ids, captureof(wildcard(super(Entity wcb))) ])) = wcb;
public Entity boundWildcardLB(entity([ *ids, wildcard(extends(Entity wcb)) ])) = zero();
public Entity boundWildcardLB(entity([ *ids, captureof(wildcard(extends(Entity wcb))) ])) = zero();
public default Entity boundWildcardLB(Entity val) = val;
@doc{EXTENSION with wildcards}
public Entity boundWildcard(entity([ *ids, wildcard() ])) = zero();
public Entity boundWildcard(entity([ *ids, wildcard(super(Entity wcb)) ])) = wcb;
public Entity boundWildcard(entity([ *ids, captureof(wildcard(super(Entity wcb))) ])) = wcb;
public Entity boundWildcard(entity([ *ids, wildcard(extends(Entity wcb)) ])) = wcb;
public Entity boundWildcard(entity([ *ids, captureof(wildcard(extends(Entity wcb))) ])) = wcb;
public default Entity boundWildcard(Entity val) = val;

@doc{Does lookup into substitution}
public Entity lookupSubsts(Substs s, Entity v) {
	map[Entity, Entity] mapOfs = ();
	if(!isEmpty(s.params))
		for(int i <- [0..size(s.params)])
			mapOfs[s.params[i]] = s.args[i];
	return mapOfs[v] ? zero();
}

@doc{Concatenates substitutions}
public Substs concat(Substs s1, Substs s2) { 
	assert(size(s1.args) == size(s1.params)); assert(size(s2.args) == size(s2.params));		
	Substs s = substs( ((!isEmpty(s1.params)) ? [ s1.args[i] | int i <- [0..size(s1.params)], s1.params[i] notin s2.params ] : []) + s2.args, 
		    	       ((!isEmpty(s1.params)) ? [ s1.params[i] | int i <- [0..size(s1.params)], s1.params[i] notin s2.params ] : []) + s2.params );
	assert(size(s.args) == size(s.params));
	return normalize(s);
}

@doc{Does propagation via type parameters}
public Substs normalize(Substs s) {
	list[Entity] args = s.args;
	list[Entity] params = s.params;
	if(isEmpty(params) || size(params) == 1) return s;
	int n = -1;
	Entity bnd = zero();
	if(int i <- [0..size(args)], 
			isTypeParameter(args[i]), Entity b := lookupSubsts(s, args[i]), b != zero()) {
		n = i;
		bnd = b;
	}
	if(n == -1) return s;
	// DEBUG: println("normalization ..."); println(s);
	Entity arg = args[n];
	args[n] = bnd;
	if(int i <- [0..size(params)], params[i] == arg) {
		args = delete(args,i);
		params = delete(params,i);
	}
	// DEBUG: println(substs(args,params));
	return normalize(substs(args,params));
}
