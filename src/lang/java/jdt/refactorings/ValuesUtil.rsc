module lang::java::jdt::refactorings::ValuesUtil

import lang::java::jdt::Java;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::JavaADT;

@doc{Returns true if an anonymous declared type}
public bool isAnonymous(Entity val) = (entity([ *ids, anonymous(loc _, Entity _) ]) := val);
@doc{Returns true if a binding to an array type}
public bool isArrayType(Entity val) = (entity([ *ids, array(Entity _) ]) := val);
@doc{Returns true if a method binding}
public bool isMethodBinding(Entity val) = ( (entity([ *ids , method(_,_,_) ]) := val) || (entity([ *ids , method(_,_,_,_) ]) := val) );
@doc{Returns true if the method binding is a constructor binding}
public bool isConstructorBinding(Entity val) = ( (entity([ *ids, constr(_) ]) := val) || (entity([ *ids, constr(_,_) ]) := val));
@doc{Returns true if a variable binding (fields, formal parameters, local variables)}							 
public bool isVariableBinding(Entity val) = ( (entity([ *ids, enumConstant(_,_) ]) := val) 
											|| (entity([ *ids, field(_,_) ]) := val) 
											|| (entity([ *ids, \parameter(_,_) ]) := val) 
											|| (entity([ *ids, variable(_,_,_) ]) := val)
											|| (entity([ *ids, \parameter(_) ]) := val) );
@doc{Returns true if a variable binding to a field}							 
public bool isFieldBinding(Entity val) = (entity([ *ids, field(_,_) ]) := val);
@doc{Returns true if a type parameter}
public bool isTypeParameter(Entity val) = ( entity([ *ids, typeParameter(_,_) ]) := val );
@doc{Returns true if a type binding (classes, interfaces, primitive types, type parameters)}
public bool isType(Entity val) = ( (entity([ *ids, class(_) ]) := val) 
								 || (entity([ *ids, class(_,_) ]) := val) 
								 || (entity([ *ids, interface(_) ]) := val) 
								 || (entity([ *ids, interface(_,_) ]) := val)
								 || (entity([ *ids, anonymousClass(_)]) := val) 
								 || (entity([ *ids, enum(_) ]) := val)
								 || (entity([ *ids, primitive(_) ]) := val)
								 || (entity([ *ids, array(_) ]) := val)
								 || (entity([ *ids, typeParameter(_,_) ]) := val)
								 || (entity([ *ids, wildcard() ]) := val)
								 || (entity([ *ids, wildcard(_) ]) := val)
								 || (entity([ *ids, captureof(_) ]) := val) );
@doc{Returns true if a wildcard binding}									
public bool isWildCardType(Entity val) = ( (entity([ *ids, wildcard() ]) := val)
										 || (entity([ *ids, wildcard(_) ]) := val)
										 || (entity([ *ids, captureof(_) ]) := val) );

@doc{Returns type parameters or type arguments}	
// Note: the constructor type values are treated separately, i.e. type parameters (type arguments) of the declaring type are taken into account									 
public list[Entity] getGenericTypes(entity([ *ids, class(_, list[Entity] params), constr(_) ])) = params;
public list[Entity] getGenericTypes(entity([ *ids, class(_), constr(list[Entity] genericTypes,_) ])) = genericTypes;
public list[Entity] getGenericTypes(entity([ *ids, class(_, list[Entity] params), constr(list[Entity] genericTypes,_) ])) = params + genericTypes;
public list[Entity] getGenericTypes(entity([ *_, method(list[Entity] genericTypes,_,_,_) ])) = genericTypes;
public list[Entity] getGenericTypes(Entity val) = [];

public bool isTypeParameter(ParameterizedEntity val) = isTypeParameter(val.genval);

public bool isTypeArgument(entity([ *ids, typeArgument(str name, context, ParameterizedEntity init, list[ParameterizedEntity] bounds) ])) = true;
public bool isTypeArgument(parameterizedentity(bindings([],[]), entity([ *ids, typeArgument(str name, context, ParameterizedEntity init, list[ParameterizedEntity] bounds) ]))) = true;
public bool isTypeArgument(_) = false;