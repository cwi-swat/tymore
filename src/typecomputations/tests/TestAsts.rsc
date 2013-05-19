module typecomputations::tests::TestAsts

import lang::java::jdt::JDT;
import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import typecomputations::tests::TestProjects;

import util::Benchmark;

import IO;

public void main1() { testAsts(eclipseSources); }

public void testAsts(list[loc] projects) { 
	int t1 = cpuTime(); 
	for(project <- projects) testAsts(project); 
	int t2 = cpuTime();
	println("cpu: <t2-t1>");
}	

private void testAsts(loc project) {
	println("calculating facts and asts...");
	//set[AstNode] cus = createAstsFromProject(project, collectBindings = false);
	cus = extractProject(project, fillASTBindings = false); 
	println("done...");
//	iprintln(cus);
	//for(AstNode cu <- cus) {
	//	visit(cu) {
	//		case AstNode n: println(n@bindings);
	//	}
	////	//iprintln(cu);
	//}
//		for(/AstNode n := cu) {
//			visit(n@bindings) {
//				case entity([*ids, package(str name)]): ;
//				case entity([ *ids, class(str name) ]): /*println("cls(n)")*/;
//     			case entity([ *ids, class(str name, list[Entity] params) ]): println("cls(n,ps)");
//     			case entity([ *ids, interface(str name) ]): /*println("intf(n)")*/;
//     			case entity([ *ids, interface(str name, list[Entity] params) ]): println("intf(n,ps)");
//     			case entity([ *ids, anonymousClass(int nr) ]): /*println("cls(n)")*/;
//     			case entity([ *ids, enum(str name) ]): /*println("cls(n)")*/;
//        
//     			case entity([ *ids, method(str name, list[Entity] params, Entity returnType) ]): /*println("meth(n, ps, rt)")*/;
//     			case entity([ *ids, constr(list[Entity] params) ]): /*println("constr(ps)")*/;
//     			case entity([ *ids, initializer() ]): /*println("init()")*/;
//     			case entity([ *ids, initializer(int nr) ]): /*println("init(nr)")*/;
//
//     			case entity([ *ids, field(str name) ]): /*println("field(n)")*/;
//     			case entity([ *ids, parameter(str name) ]): /*println("param(n)")*/;
//     			case entity([ *ids, variable(str name, int id) ]): /*println("var(n,id)")*/;
//     			case entity([ *ids, enumConstant(str name) ]): /*println("enumC(n)")*/;
//     
//     			case entity([ *ids, primitive(PrimitiveType primType) ]): /*println("primitiveT()")*/;
//     			case entity([ *ids, array(Entity elementType) ]): /*println("array()")*/;
//     
//     			case entity([ *ids, typeParameter(str name) ]): println("tparam()");
//     			case entity([ *ids, wildcard() ]): println("wcard()");
//     			case entity([ *ids, wildcard(Bound bound) ]): println("wcard(b)");
//     			case entity([ *ids, captureof(Entity wcard)]): println("capture(wcard)");
//     			case Entity e: { println("unknown: <e>; <n>"); throw "unknown"; }
//			}
//		}
//	}
}