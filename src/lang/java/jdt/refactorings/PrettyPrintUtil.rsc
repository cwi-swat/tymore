module lang::java::jdt::refactorings::PrettyPrintUtil

import Prelude;
import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;

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
public str prettyprint(Id::typeParameter(str name)) = "<name> (type parameter)";
public str prettyprint(wildcard()) = "!";
public str prettyprint(wildcard(super(Entity b))) = "! super <prettyprint(b)>";
public str prettyprint(wildcard(extends(Entity b))) = "! extends <prettyprint(b)>";
public str prettyprint(captureof(Entity wildCard)) = "captureof <prettyprint(wildCard)>";

public str prettyprint(PrimitiveType pt) = "<pt>";

public str prettyprint(method(list[Entity] genericTypes, str name, list[Entity] params, Entity returnType)) = "<if(!isEmpty(genericTypes)){>\<<for(int i <- [0..size(genericTypes)]){><if(i != size(genericTypes)-1){><prettyprint(genericTypes[i])>,<}else{><prettyprint(genericTypes[i])><}><}>\><}> <prettyprint(returnType)> <name>(<if(size(params) != 0){><for(int i <- [0..size(params)-1]){><if(i != size(params)-1){><prettyprint(params[i])>,<}else{><prettyprint(params[i])><}><}><}else{><}>)";
public str prettyprint(constr(list[Entity] genericTypes, list[Entity] params)) = "<if(!isEmpty(genericTypes)){>\<<for(int i <- [0..size(genericTypes)]){><if(i != size(genericTypes)-1){><prettyprint(genericTypes[i])>,<}else{><prettyprint(genericTypes[i])><}><}>\><}> (<if(size(params) != 0){><for(int i <- [0..size(params)]){><if(i != size(params)-1){><prettyprint(params[i])>,<}else{><prettyprint(params[i])><}><}><}else{><}>)";
public str prettyprint(field(str name, _)) = "<name> (field)";
public str prettyprint(Id::parameter(str name, _)) = "<name> (parameter)";
public str prettyprint(variable(str name, _,_)) = name;
public str prettyprint(enumConstant(str name, _)) = "enum (<name>)";
public str prettyprint(Id::typeParameter(str name, _)) = "<name> (type parameter)";

public str prettyprint(anonymous(loc location, Entity declaredType)) = "anonymous(<prettyprint(declaredType)>)";
public str prettyprint(inherits(Entity declaredType)) = "inherits(<prettyprint(declaredType)>)";
public str prettyprint(Id::decl()) = "decl()";
public str prettyprint(Id::parameter(int i)) = "parameter(<i>)";

public str prettyprint(Id::upper()) = "UPPER";
public str prettyprint(Id::lower()) = "LOWER";
public str prettyprint(Id::upper(_)) = "UPPER";
public str prettyprint(Id::lower(_)) = "LOWER";
public str prettyprint(Id::typeArgument(str name, c, PEntity init)) = "<name>(<prettyprint(c)>)";
public str prettyprint(Id::typeArgument(str name, c, Entity initv)) = "<name>(<prettyprint(c)> --- <prettyprint(initv)>)";

public str prettyprint(bindings(list[PEntity] args, list[Entity] params)) = "[ <for(arg<-args){><prettyprint(arg)>;<}> <for(param<-params){><prettyprint(param)>;<}> ]";
public str prettyprint(pentity(Bindings bindings, Entity genval)) = "<if((bindings.args != []) && (bindings.params != [])){><prettyprint(bindings)><}><prettyprint(genval)>";

public str prettyprint(substs(list[Entity] args, list[Entity] params)) = "[ <for(arg<-args){><prettyprint(arg)>;<}> <for(param<-params){><prettyprint(param)>;<}> ]";
public str prettyprint(pentity(Substs s, Entity genval)) = "<if((s.args != []) && (s.params != [])){><prettyprint(s)><}><prettyprint(genval)>";

public str prettyprint(AstNode astNode) = readFile(astNode@location);

public default str prettyprint(value v) { throw "undeclared constructor: <v>"; }

public void tracer(bool condition, str msg) {
	if(condition) println("TRACER: " + msg);
}