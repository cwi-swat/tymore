module lang::java::jdt::refactorings::PrettyPrintUtil

import Prelude;
import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;

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
//public str prettyprint(\parameter(str name)) = "<name> (parameter)";
public str prettyprint(variable(str name, _)) = name;
public str prettyprint(enumConstant(str name)) = "enum (<name>)";
public str prettyprint(field(str name, _)) = "<name> (field)";
//public str prettyprint(\parameter(str name, _)) = "<name> (parameter)";
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
		case parameter(str name): return "<name> (parameter)";
		case parameter(str name, _): return "<name> (parameter)";
		case parameter(int i): return "parameter(<i>)";
		case typeParameter(str name,_): return "<name> (type parameter)";
		
		case typeArgument(str name, context, PEntity init, list[PEntity] bounds): return "<name>(<prettyprint(context)>)" /* "<name>(<prettyprint(init)>)" "<name>(<prettyprint(context)>)[-\> <prettyprint(init)> (init); <for(Entity b<-bounds){><prettyprint(b)>;<}>]"*/;
	}
}
public str prettyprint(anonymous(loc location, Entity declaredType)) = "anonymous(<prettyprint(declaredType)>)";
public str prettyprint(inherits(Entity declaredType)) = "inherits(<prettyprint(declaredType)>)";
public str prettyprint(decl()) = "decl()";
//public str prettyprint(\parameter(int i)) = "parameter(<i>)";
//public str prettyprint(byte()) = "byte";
//public str prettyprint(short()) = "short";
//public str prettyprint(\int()) = "int";
//public str prettyprint(long()) = "long";
//public str prettyprint(float()) = "float";
//public str prettyprint(double()) = "double";
//public str prettyprint(char()) = "char";
//public str prettyprint(boolean()) = "boolean";
//public str prettyprint(\void()) = "void";
//public str prettyprint(null()) = "null";
public str prettyprint(PrimitiveType t) {
	switch(t) {
		case byte(): return "byte";
		case short(): return "short";
		case \int(): return "int";
		case long(): return "long";
		case float(): return "float";
		case double(): return "double";
		case char(): return "char";
		case boolean(): return "boolean";
		case \void(): return "void";
		case null(): return "null";
	}
	return "<t>";
}

public str prettyprint(bindings(list[PEntity] args, list[Entity] params)) = "[ <for(arg<-args){><prettyprint(arg)>;<}> <for(param<-params){><prettyprint(param)>;<}> ]";
public str prettyprint(pentity(Bindings bindings, Entity genval)) = "<if((bindings.args != []) && (bindings.params != [])){><prettyprint(bindings)><}><prettyprint(genval)>";

public default str prettyprint(AstNode astNode) = readFile(astNode@location);