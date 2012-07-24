/*
 * The module defines the domain of type values:
 * - their algebraic representation: Entity; and
 * - their functional semantcis: Entity (Entity) eval; Entity (AstNode) lookup; 
 * 								 set[Entity] (Entity) overrides; 
 * 								 Entity (Entity) decl; (unique representation of the declaring type of a declaration) 
 * 								 Entity (Entity, int i) param; (unique representation of the declaring type of a declaration parameter) 
 */
module typecomputations::TypeValues

import List;
import Node;
import Relation;
import Set;

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;

import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;

import IO;

/*
 * Imported compilation unit facts format
 */
public alias CompilUnit = map[str, rel[Entity, Entity]];

/*
 * Helper functions
 */
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
// in case of constructors, i.e. new A().new B(), declaring type is evaluated to the type that declares the type, 
// objects of which the constructor creates 
public Entity eval(entity([ *ids, constr(_), decl() ])) = eval(entity(ids + decl()));
public Entity eval(entity([ *ids, constr(_,_), decl() ])) = eval(entity(ids + decl()));
public Entity eval(entity([ *ids, id, decl() ])) = entity(ids);
public Entity eval(entity([ *_, constr(list[Entity] params), \parameter(int i) ])) = params[i];
public Entity eval(entity([ *_, method(_, list[Entity] params, _), \parameter(int i) ])) = params[i];
public Entity eval(entity([ *_, constr(_, list[Entity] params), \parameter(int i) ])) = params[i];
public Entity eval(entity([ *_, method(_,_, list[Entity] params,_), \parameter(int i) ])) = params[i];
public default Entity eval(Entity val) = val;
@doc{ Basic lookup semantics, the typed terms are: expressions (e) and declarations (d) }
public Entity lookup(e:arrayAccess(_,_)) = getType(e);
public Entity lookup(e:arrayCreation(_,_,_)) = getType(e);
public Entity lookup(e:arrayInitializer(_)) = getType(e);
public Entity lookup(e:assignment(AstNode le,_)) = lookup(le);
public Entity lookup(e:booleanLiteral(_)) = getType(e);
public Entity lookup(e:castExpression(_,_)) = entity([anonymous(e@location, getType(e))]);
public Entity lookup(e:characterLiteral(_)) = getType(e);
public Entity lookup(e:classInstanceCreation(_,_,_,_,_)) = e@bindings["methodBinding"];
public Entity lookup(e:conditionalExpression(_,_,_)) = getType(e); 
public Entity lookup(s:constructorInvocation(_,_)) = s@bindings["methodBinding"];
public Entity lookup(e:fieldAccess(_,_)) = e@bindings["variableBinding"]; 
public Entity lookup(e:infixExpression(_,_,_,_)) = getType(e);
public Entity lookup(e:instanceofExpression(_,_)) = getType(e);
public Entity lookup(e:markerAnnotation(_)) = getType(e);
public Entity lookup(e:methodInvocation(_,_,_,_)) = e@bindings["methodBinding"]; 
public Entity lookup(e:normalAnnotation(_,_)) = getType(e);
public Entity lookup(e:nullLiteral()) = getType(e);
public Entity lookup(e:numberLiteral(_)) = getType(e);
public Entity lookup(e:parenthesizedExpression(_)) = getType(e);
public Entity lookup(e:postfixExpression(_,_)) = getType(e);
public Entity lookup(e:prefixExpression(_,_)) = getType(e);
public Entity lookup(e:qualifiedName(qualifier,_)) = ("variableBinding" in e@bindings && !isArrayType(getType(qualifier))) ? e@bindings["variableBinding"] : getType(e);  
public Entity lookup(e:simpleName(_)) = ("variableBinding" in e@bindings && !isArrayType(getType(e))) ? e@bindings["variableBinding"] : getType(e); 
public Entity lookup(e:singleMemberAnnotation(_,_)) = getType(e);
public Entity lookup(e:stringLiteral(_)) = getType(e);
public Entity lookup(s:superConstructorInvocation(_,_,_)) = s@bindings["methodBinding"]; 
public Entity lookup(e:superFieldAccess(_,_)) = e@bindings["variableBinding"]; 
public Entity lookup(e:superMethodInvocation(_,_,_,_)) = e@bindings["methodBinding"]; 
public Entity lookup(e:thisExpression(_)) = getType(e); 
public Entity lookup(e:typeLiteral(_)) = getType(e); 
public Entity lookup(e:variableDeclarationExpression(_,_,_)) = getType(e); 
public Entity lookup(d:anonymousClassDeclaration(_)) = getType(e);
public Entity lookup(d:typeDeclaration(_,_,_,_,_,_,_)) = getType(e);
public Entity lookup(d:methodDeclaration(_,_,_,_,_,_,_)) = getType(e);
public Entity lookup(d:singleVariableDeclaration(_,_,_,_,_)) = d@bindings["variableBinding"];
public Entity lookup(d:variableDeclarationFragment(_,_)) = d@bindings["variableBinding"];
public default Entity lookup(AstNode t) { throw "The term <t> does not have the lookup semantics !"; }
@doc{Basic typing semantics}
public Entity getType(AstNode t) = t@bindings["typeBinding"];
@doc{Overrides semantics}
public set[Entity] (Entity) overrides(CompitUnit facts) = set[Entity] (Entity val) { return facts["overrides_func"][val];};
@doc{Declaring type semantics}
public Entity decl(Entity val) = entity(val.id + decl());
@doc{Declared parameter type semantics}
public Entity param(Entity val, int i) = entity(val.id + \parameter(i));

public list[Entity] getGenericTypes(entity([ *ids, class(_, list[Entity] params), constr(_) ])) = params;
public list[Entity] getGenericTypes(entity([ *ids, class(_), constr(list[Entity] genericTypes,_) ])) = genericTypes;
public list[Entity] getGenericTypes(entity([ *ids, class(_, list[Entity] params), constr(list[Entity] genericTypes,_) ])) = params + genericTypes;
public list[Entity] getGenericTypes(entity([ *_, method(list[Entity] genericTypes,_,_,_) ])) = genericTypes;
public list[Entity] getGenericTypes(Entity val) = [];


@doc{Extension of the Rascal Entity data type with type argument variables}
data Id = typeArgument(str name, Entity context, ParameterizedEntity init, list[ParameterizedEntity] bounds)
		| typeArgument(str name, AstNode context, ParameterizedEntity init, list[ParameterizedEntity] bounds);

data Bindings = bindings(list[ParameterizedEntity] args, list[Entity] params);
data ParameterizedEntity = parameterizedentity(Bindings bindings, Entity genericval);
public ParameterizedEntity parameterizedentity(Entity genericval) = parameterizedentity(bindings([],[]), genericval);

public ParameterizedEntity object = parameterizedentity(bindings([], []), entity([package("java"), package("lang"), class("Object")]));
public ParameterizedEntity zero = parameterizedentity(bindings([], []), entity([]));

// ----- Bunch of prettyprint utility functions (Not Important!) --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------			 
public str prettyprint(entity(list[Id] ids)) = "<if(!isEmpty(ids)){><for(int i <- [0..size(ids)-1]){><if(i != size(ids)-1){><if(prettyprint(ids[i]) != "") {><prettyprint(ids[i])>.<}><}else{><prettyprint(ids[i])><}><}><}else{>_<}>";
public str prettyprint(package(str name)) = "";
public str prettyprint(class(str name)) = name;
public str prettyprint(class(str name, list[Entity] params)) = "<name>\<<for(int i <- [0..size(params)-1]){><if(i != size(params)-1){><prettyprint(params[i])>,<}else{><prettyprint(params[i])><}><}>\>";
public str prettyprint(interface(str name)) = name;
public str prettyprint(interface(str name, list[Entity] params)) = "<name>\<<for(int i <- [0..size(params)-1]){><if(i != size(params)-1){><prettyprint(params[i])>,<}else{><prettyprint(params[i])><}><}>\>"; 
public str prettyprint(anonymousClass(int nr)) = "anonymousClass(<nr>)";
public str prettyprint(enum(str name)) = name;
public str prettyprint(method(str name, list[Entity] params, Entity returnType)) = "<prettyprint(returnType)> <name>(<if(size(params) != 0){><for(int i <- [0..size(params)-1]){><if(i != size(params)-1){><prettyprint(params[i])>,<}else{><prettyprint(params[i])><}><}><}else{><}>)";
public str prettyprint(constr(list[Entity] params)) = "(<if(size(params) != 0){><for(int i <- [0..size(params)-1]){><if(i != size(params)-1){><prettyprint(params[i])>,<}else{><prettyprint(params[i])><}><}><}else{><}>)";
public str prettyprint(method(list[Entity] genericTypes, str name, list[Entity] params, Entity returnType)) = "<if(!isEmpty(genericTypes)){>\<<for(int i <- [0..size(genericTypes)-1]){><if(i != size(genericTypes)-1){><prettyprint(genericTypes[i])>,<}else{><prettyprint(genericTypes[i])><}><}>\><}> <prettyprint(returnType)> <name>(<if(size(params) != 0){><for(int i <- [0..size(params)-1]){><if(i != size(params)-1){><prettyprint(params[i])>,<}else{><prettyprint(params[i])><}><}><}else{><}>)";
public str prettyprint(constr(list[Entity] genericTypes, list[Entity] params)) = "<if(!isEmpty(genericTypes)){>\<<for(int i <- [0..size(genericTypes)-1]){><if(i != size(genericTypes)-1){><prettyprint(genericTypes[i])>,<}else{><prettyprint(genericTypes[i])><}><}>\><}> (<if(size(params) != 0){><for(int i <- [0..size(params)-1]){><if(i != size(params)-1){><prettyprint(params[i])>,<}else{><prettyprint(params[i])><}><}><}else{><}>)";
public str prettyprint(field(str name)) = "<name> (field)";
public str prettyprint(\parameter(str name)) = "<name> (parameter)";
public str prettyprint(variable(str name, _)) = name;
public str prettyprint(enumConstant(str name)) = "enum (<name>)";
public str prettyprint(field(str name, _)) = "<name> (field)";
public str prettyprint(\parameter(str name, _)) = "<name> (parameter)";
public str prettyprint(variable(str name, _,_)) = name;
public str prettyprint(enumConstant(str name, _)) = "enum (<name>)";
public str prettyprint(primitive(PrimitiveType primType)) = "<prettyprint(primType)>";
public str prettyprint(array(Entity elementType)) = "<prettyprint(elementType)>[]";
public str prettyprint(wildcard()) = "!";
public str prettyprint(wildcard(super(Entity b))) = "! super <prettyprint(b)>";
public str prettyprint(wildcard(extends(Entity b))) = "! extends <prettyprint(b)>";
public str prettyprint(captureof(Entity wildCard)) = "captureof <prettyprint(wildCard)>";
public default str prettyprint(Id id) {
	switch(id) {
		case initializer(): return "initializer";
		case initializer(int nr): return "initializer(<nr>)";
		case typeParameter(str name,_): return "<name> (type parameter)";
		
		case typeArgument(str name, context, ParameterizedEntity init, list[ParameterizedEntity] bounds): return "<name>(<prettyprint(context)>; (init) <prettyprint(init)>)" /* "<name>(<prettyprint(init)>)" "<name>(<prettyprint(context)>)[-\> <prettyprint(init)> (init); <for(Entity b<-bounds){><prettyprint(b)>;<}>]"*/;
	}
}
public str prettyprint(anonymous(loc location, Entity declaredType)) = "anonymous(<prettyprint(declaredType)>)";
public str prettyprint(inherits(Entity declaredType)) = "inherits(<prettyprint(declaredType)>)";
public str prettyprint(decl()) = "decl()";
public str prettyprint(\parameter(int i)) = "parameter(<i>)";

public str prettyprint(byte()) = "byte";
public str prettyprint(short()) = "short";
public str prettyprint(\int()) = "int";
public str prettyprint(long()) = "long";
public str prettyprint(float()) = "float";
public str prettyprint(double()) = "double";
public str prettyprint(char()) = "char";
public str prettyprint(boolean()) = "boolean";
public str prettyprint(\void()) = "void";
public str prettyprint(null()) = "null";

public str prettyprint(bindings(list[ParameterizedEntity] args, list[Entity] params)) = "[ <for(arg<-args){><prettyprint(arg)>;<}> <for(param<-params){><prettyprint(param)>;<}> ]";
public str prettyprint(parameterizedentity(Bindings bindings, Entity genericval)) = "<if((bindings.args != []) && (bindings.params != [])){><prettyprint(bindings)><}><prettyprint(genericval)>";

public str prettyprint(AstNode astNode) = readFile(astNode@location);