module lang::java::jdt::refactorings::ValuesUtil

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;

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
public bool isTypeArgument(entity([ *ids, typeArgument(str name, _, PEntity init) ])) = true;
public bool isTypeArgument(entity([ *ids, typeArgument(str name, _, PEntity init), upper() ])) = true;
public bool isTypeArgument(entity([ *ids, typeArgument(str name, _, PEntity init), lower() ])) = true;
public bool isTypeArgument(pentity(Bindings _, entity([ *ids, typeArgument(str name, _, PEntity init) ]))) = true;
public bool isTypeArgument(pentity(Bindings _, entity([ *ids, typeArgument(str name, _, PEntity init), upper() ]))) = true;
public bool isTypeArgument(pentity(Bindings _, entity([ *ids, typeArgument(str name, _, PEntity init), lower() ]))) = true;

public bool isTypeArgument(entity([ *ids, typeArgument(str name, _, Entity _) ])) = true;
public bool isTypeArgument(entity([ *ids, typeArgument(str name, _, Entity _), upper() ])) = true;
public bool isTypeArgument(entity([ *ids, typeArgument(str name, _, Entity _), lower() ])) = true;

public default bool isTypeArgument(_) = false;

public Entity getUpperB(ta:entity([ *ids, typeArgument(_,_,_), upper() ])) = ta;
public Entity getUpperB(ta:entity([ *ids, typeArgument(_,_,_), lower() ])) = ta;
public Entity getUpperB(ta:entity([ *ids, typeArgument(_,_,_) ])) = entity(ta.id + upper());
public Entity getLowerB(ta:entity([ *ids, typeArgument(_,_,_), upper() ])) = ta;
public Entity getLowerB(ta:entity([ *ids, typeArgument(_,_,_), lower() ])) = ta;
public Entity getLowerB(ta:entity([ *ids, typeArgument(_,_,_) ])) = entity(ta.id + lower());

public Entity getTypeParameter(entity([ *ids, typeArgument(str name, _,_) ])) = entity([typeParameter(name)]);
public Entity getTypeParameter(entity([ *ids, typeArgument(str name, _,_), upper() ])) = entity([typeParameter(name)]);
public Entity getTypeParameter(entity([ *ids, typeArgument(str name, _,_), lower() ])) = entity([typeParameter(name)]);

public Entity getInit(entity([ *ids, typeArgument(str name, _, PEntity init) ])) = init@paramval;
public Entity getInit(entity([ *ids, typeArgument(str name, _, PEntity init), upper() ])) = boundWcardUB(init@paramval);
public Entity getInit(entity([ *ids, typeArgument(str name, _, PEntity init), lower() ])) = boundWcardLB(init@paramval);
public default Entity getInit(_) = pzero();

public Entity boundWcardUB(entity([ *ids, wildcard() ])) = zero();
public Entity boundWcardUB(entity([ *ids, wildcard(extends(Entity wcb)) ])) = boundWcardUB(wcb);
public Entity boundWcardUB(entity([ *ids, captureof(wildcard(extends(Entity wcb))) ])) = boundWcardUB(wcb);
public Entity boundWcardUB(entity([ *ids, wildcard(super(Entity wcb)) ])) = zero();
public Entity boundWcardUB(entity([ *ids, captureof(wildcard(super(Entity wcb))) ])) = zero();
public default Entity boundWcardUB(Entity val) = val;

public Entity boundWcardLB(entity([ *ids, wildcard() ])) = zero();
public Entity boundWcardLB(entity([ *ids, wildcard(super(Entity wcb)) ])) = boundWcardLB(wcb);
public Entity boundWcardLB(entity([ *ids, captureof(wildcard(super(Entity wcb))) ])) = boundWcardLB(wcb);
public Entity boundWcardLB(entity([ *ids, wildcard(extends(Entity wcb)) ])) = returnBL(zero());
public Entity boundWcardLB(entity([ *ids, captureof(wildcard(extends(Entity wcb))) ])) = returnBL(zero());
public default Entity boundWcardLB(Entity val) = val;

@doc{Gets the generic part of a parameterized type}
public PEntity getGenericVal(PEntity val) = pentity(val.genval)[@paramval=val.genval];

@doc{Concatenates bindings}
public Bindings concat(Bindings b1, Bindings b2) { 
	assert(size(b1.args) == size(b1.params)); 
	assert(size(b2.args) == size(b2.params));		
	bs = bindings( ((!isEmpty(b1.params)) ? [ b1.args[i] | int i <- [0..size(b1.params)], b1.params[i] notin b2.params ] : []) + b2.args, 
		    	   ((!isEmpty(b1.params)) ? [ b1.params[i] | int i <- [0..size(b1.params)], b1.params[i] notin b2.params ] : []) + b2.params );
	assert(size(bs.args) == size(bs.params));
	return bs;
}

@doc{Concatenates bindings}
public Substs concat(Substs s1, Substs s2) { 
	assert(size(s1.args) == size(s1.params)); 
	assert(size(s2.args) == size(s2.params));		
	s = substs( ((!isEmpty(s1.params)) ? [ s1.args[i] | int i <- [0..size(s1.params)], s1.params[i] notin s2.params ] : []) + s2.args, 
		    	((!isEmpty(s1.params)) ? [ s1.params[i] | int i <- [0..size(s1.params)], s1.params[i] notin s2.params ] : []) + s2.params );
	assert(size(s.args) == size(s.params));
	return s;
}

@doc{Essential mapping between 'Entity' and 'PEntity' domains (with explicit substitutions of type parameters)}
@doc{Recursive function that maps to the representation with explicit type parameter substitution}	
public PEntity (Entity) toGens(Mapper mapper) 
	= PEntity (Entity val) { 
		if(val == zero()) 
			return pzero(); 
		if(isTypeParameter(val) || isWildCardType(val) || isTypeArgument(val)) 
			return pentity(val)[@paramval=val];
		if(entity([ *ids, anonymous(_,_)]) := val) 
			return pentity(val)[@paramval=val];
		if(entity([ *ids, decl() ]) := val) {
			PEntity pval = toGens(mapper)(entity(ids));
			return pentity(pval.bindings, decl(pval.genval))[@paramval = val];
		}
		if(entity([ *ids, \parameter(int i) ]) := val) {
			PEntity pval = toGens(mapper)(entity(ids));
			return pentity(pval.bindings, param(i)(pval.genval))[@paramval = val];
		}
		tuple[tuple[list[Entity], list[Entity]], Entity] v = mapper[val];
		Entity genval = v[1]; 
		list[Entity] args = v[0][0]; 
		list[Entity] params = v[0][1];
		
		assert(size(args)==size(params));
		
		if(isEmpty(params)) 
			return pentity(bindings([], []), genval)[@paramval=val];
			
		list[PEntity] pargs = [ (entity([]) := args[i]) ? pzero() : toGens(mapper)(args[i]) | int i <- [0..size(params)] ];
		return pentity(bindings(pargs, params), genval)[@paramval=val]; 
	};
public map[Entity, PEntity] memoMkSubstsExplicit = ();
@doc{Makes the semantics with the explicit substitutions of type parameters}
public PEntity mkSubstsExplicit(Mapper mapper, Entity val) 
	= memoMkSubstsExplicit[val] ? { PEntity pval = toGens(mapper)(val); memoMkSubstsExplicit[val] = pval; return pval; };

@doc{Returns true if a raw type}
public bool isRawType(Mapper mapper, Entity val) = pzero() in mkSubstsExplicit(mapper, val).bindings.args;
@doc{Lifts functions to 'PEntity' domain}
public PEntity (PEntity) pmap(Mapper mapper, Entity (Entity) f) = PEntity (PEntity pval) { return mkSubstsExplicit(mapper, f(pval@paramval)); };
public set[PEntity] (PEntity) pmap(Mapper mapper, set[Entity] (Entity) f) = set[PEntity] (PEntity pval) { return { mkSubstsExplicit(mapper, v) | Entity v <- f(pval@paramval) }; };

