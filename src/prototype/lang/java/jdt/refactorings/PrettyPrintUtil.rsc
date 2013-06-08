@license{
  Copyright (c) 2009-2011 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - A.Izmaylova@cwi.nl}
module prototype::lang::java::jdt::refactorings::PrettyPrintUtil

import Prelude;
import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import prototype::lang::java::jdt::refactorings::Java;
import prototype::lang::java::jdt::refactorings::JavaADT;

public str prettyprint(entity(list[Id] ids)) = "<if(!isEmpty(ids)){><for(int i <- [0..size(ids)]){><if(i != size(ids)-1){><if(prettyprint(ids[i]) != "") {><prettyprint(ids[i])>.<}><}else{><prettyprint(ids[i])><}><}><}else{>_<}>";

public str prettyprint(package(str name)) = "";
public str prettyprint(class(str name)) = name;
public str prettyprint(class(str name, list[Entity] params)) = "<name>\<<for(int i <- [0..size(params)]){><if(i != size(params)-1){><prettyprint(params[i])>,<}else{><prettyprint(params[i])><}><}>\>";
public str prettyprint(interface(str name)) = name;
public str prettyprint(interface(str name, list[Entity] params)) = "<name>\<<for(int i <- [0..size(params)]){><if(i != size(params)-1){><prettyprint(params[i])>,<}else{><prettyprint(params[i])><}><}>\>"; 
public str prettyprint(anonymousClass(int nr)) = "anonymousClass(<nr>)";
public str prettyprint(enum(str name)) = name;
public str prettyprint(method(str name, list[Entity] params, Entity returnType)) = "<prettyprint(returnType)> <name>(<if(size(params) != 0){><for(int i <- [0..size(params)]){><if(i != size(params)-1){><prettyprint(params[i])>,<}else{><prettyprint(params[i])><}><}><}else{><}>)";
public str prettyprint(constr(list[Entity] params)) = "(<if(size(params) != 0){><for(int i <- [0..size(params)]){><if(i != size(params)-1){><prettyprint(params[i])>,<}else{><prettyprint(params[i])><}><}><}else{><}>)";
public str prettyprint(Id::initializer()) = "initializer";
public str prettyprint(Id::initializer(int nr)) = "initializer(<nr>)";
public str prettyprint(field(str name)) = "<name> (field)";
public str prettyprint(Id::parameter(str name)) = "<name> (parameter)";
public str prettyprint(variable(str name, _)) = name;
public str prettyprint(enumConstant(str name)) = "enum (<name>)";
public str prettyprint(primitive(PrimitiveType primType)) = "<prettyprint(primType)>";
public str prettyprint(array(Entity elementType)) = "<prettyprint(elementType)>[]";
public str prettyprint(wildcard()) = "!";
public str prettyprint(wildcard(super(Entity b))) = "! super <prettyprint(b)>";
public str prettyprint(wildcard(extends(Entity b))) = "! extends <prettyprint(b)>";
public str prettyprint(captureof(Entity wildCard)) = "captureof <prettyprint(wildCard)>";

public str prettyprint(PrimitiveType pt) = "<prettyprint(pt)>";

public str prettyprint(PrimitiveType::byte()) = "byte";
public str prettyprint(PrimitiveType::short()) = "short";
public str prettyprint(PrimitiveType::\int()) = "int";
public str prettyprint(PrimitiveType::long()) = "long";
public str prettyprint(PrimitiveType::float()) = "float";
public str prettyprint(PrimitiveType::double()) = "double";
public str prettyprint(PrimitiveType::char()) = "char";
public str prettyprint(PrimitiveType::boolean()) = "boolean";
public str prettyprint(PrimitiveType::\void()) = "void";
public str prettyprint(PrimitiveType::null()) = "null";

public str prettyprint(method(list[Entity] genericTypes, str name, list[Entity] params, Entity returnType)) = "<if(!isEmpty(genericTypes)){>\<<for(int i <- [0..size(genericTypes)]){><if(i != size(genericTypes)-1){><prettyprint(genericTypes[i])>,<}else{><prettyprint(genericTypes[i])><}><}>\><}> <prettyprint(returnType)> <name>(<if(size(params) != 0){><for(int i <- [0..size(params)]){><if(i != size(params)-1){><prettyprint(params[i])>,<}else{><prettyprint(params[i])><}><}><}else{><}>)";
public str prettyprint(constr(list[Entity] genericTypes, list[Entity] params)) = "<if(!isEmpty(genericTypes)){>\<<for(int i <- [0..size(genericTypes)]){><if(i != size(genericTypes)-1){><prettyprint(genericTypes[i])>,<}else{><prettyprint(genericTypes[i])><}><}>\><}> (<if(size(params) != 0){><for(int i <- [0..size(params)]){><if(i != size(params)-1){><prettyprint(params[i])>,<}else{><prettyprint(params[i])><}><}><}else{><}>)";
public str prettyprint(field(str name, _)) = "<name> (field)";
public str prettyprint(Id::parameter(str name, _)) = "<name> (parameter)";
public str prettyprint(variable(str name, _,_)) = name;
public str prettyprint(enumConstant(str name, _)) = "enum (<name>)";
public str prettyprint(Id::typeParameter(str name)) = "<name> (type parameter)";

public str prettyprint(anonymous(loc location, Entity declaredType)) = "anonymous(<prettyprint(declaredType)> <location.begin.line> <location.begin.column>)";
public str prettyprint(inherits(Entity declaredType)) = "inherits(<prettyprint(declaredType)>)";
public str prettyprint(Id::decl()) = "decl()";
public str prettyprint(Id::parameter(int i)) = "parameter(<i>)";

public str prettyprint(Id::upper(Entity init)) = "UPPER(<prettyprint(init)>)";
public str prettyprint(Id::lower(Entity init)) = "LOWER(<prettyprint(init)>)";
public str prettyprint(Id::typeArgument(str name, c, Entity init)) = "<name>(<prettyprint(c)> - <prettyprint(init)>)";
public str prettyprint(tuple[str,str] c) = "<c[0]> <c[1]>";

public str prettyprint(substs(list[Entity] args, list[Entity] params)) = "[ <for(arg<-args){><prettyprint(arg)>;<}> <for(param<-params){><prettyprint(param)>;<}> ]";
public str prettyprint(pentity(Substs s, Entity genval)) = "<if((s.args != []) && (s.params != [])){><prettyprint(s)><}><prettyprint(genval)>";

public str prettyprint(AstNode astNode) = ("location" in getAnnotations(astNode)) ? readFile(astNode@location) : "this";

public default str prettyprint(value v) { throw "undeclared constructor: <v>"; }

public void tracer(bool condition, str msg) {
	if(condition) println("TRACER: " + msg);
}