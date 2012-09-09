module lang::java::jdt::refactorings::ValuesUtil

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;

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
public bool isTypeParameter(Entity val) = ( entity([ *ids, typeParameter(_,_) ]) := val );
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
public list[Entity] getGenericTypes(Entity val) = [];
@doc{Returns the type parameters of a generic type or type arguments of a parameterized type}
public list[Entity] getTypeParamsOrArgs(entity([ *ids, class(_, list[Entity] params) ])) = params;
public list[Entity] getTypeParamsOrArgs(entity([ *ids, interface(_, list[Entity] params) ])) = params;
public list[Entity] getTypeParamsOrArgs(Entity val) = [];
@doc{Returns true if a type parameter}
public bool isTypeParameter(PEntity val) = isTypeParameter(val.genval);
@doc{Returns true if a type argument value}
public bool isTypeArgument(entity([ *ids, typeArgument(str name, context, PEntity init, list[PEntity] bounds) ])) = true;
public bool isTypeArgument(pentity(Bindings _, entity([ *ids, typeArgument(str name, context, PEntity init, list[PEntity] bounds) ]))) = true;
public bool isTypeArgument(_) = false;