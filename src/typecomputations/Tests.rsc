module typecomputations::Tests

import List;
import Node;
import Relation;
import Set;

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::JavaADT;
import lang::java::jdt::refactorings::JDT4Refactorings;

import typecomputationbasedframework4refactorings::TypeValues;
import typecomputationbasedframework4refactorings::TypeValuesPlusGens;
import typecomputationbasedframework4refactorings::TypeComputations;
import typecomputationbasedframework4refactorings::TypeComputationsPlusGens;
import typecomputationbasedframework4refactorings::SetComputationOfConstraints;

import typecomputationbasedframework4refactorings::testprojects::TestProjects;

import IO;


public alias CompilUnit = map[str, rel[Entity, Entity]];

public void testComputations(list[loc] projects) { for(project <- projects) testComputations(project); }	

private int cn = 0;

private void testComputations(loc project) {
	println("calculating facts and asts...");
	set[AstNode] compilationUnits = createAstsFromProject(project); 
	println("done...");
	for(AstNode cu <- compilationUnits) {
		cn += 1;
		println(cu@location);
		
		CompilUnit typeComputationModel = cu@typeComputationModel;
		map[Entity, tuple[ tuple[list[Entity], list[Entity]], Entity ]] parameterizedTypesSemantics = cu@parameterizedTypesSemantics;
		
		/*
		 * Building functional computational model
		 */
		tuple[ tuple[list[Entity], list[Entity]], Entity ] (Entity) mapper 
			= tuple[ tuple[list[Entity], list[Entity]], Entity ] (Entity val) { return parameterizedTypesSemantics[val]; };
			
		ParameterizedEntity (Entity) toGens = ParameterizedEntity (Entity val) { return toGenerics(mapper)(val); };
		
		rel[ParameterizedEntity, ParameterizedEntity] evaluation_semantics = { <toGens(val1), toGens(val2)> | <val1, val2> <- typeComputationModel["evaluation_func"] };
		//rel[ParameterizedEntity, ParameterizedEntity] declares_semantics   = { <toGens(val1), toGens(val2)> | <val1, val2> <- typeComputationModel["declares_func"] };
		//rel[ParameterizedEntity, ParameterizedEntity] supertypes_semantics = { <toGens(val1), toGens(val2)> | <val1, val2> <- typeComputationModel["supertypes_func"] };
		//rel[ParameterizedEntity, ParameterizedEntity] overrides_semantics  = { <toGens(val1), toGens(val2)> | <val1, val2> <- typeComputationModel["overrides_func"] };
		
		ParameterizedEntity (AstNode) lookup_func                       = lookup(toGens);
		ParameterizedEntity (ParameterizedEntity) evaluation_func       = eval(toGens);
		//set[ParameterizedEntity] (ParameterizedEntity) declares_func    = set[ParameterizedEntity] (ParameterizedEntity val) { return declares_semantics[val]; };
		//set[ParameterizedEntity] (ParameterizedEntity) supertypes_func  = set[ParameterizedEntity] (ParameterizedEntity val) { return supertypes_semantics[val]; };
		//set[ParameterizedEntity] (ParameterizedEntity) overrides_func   = set[ParameterizedEntity] (ParameterizedEntity val) { return overrides_semantics[val]; };
		
		//println("<typeComputationModel["declares_func"]>");
		for(decl <- cu.typeDeclarations) testComputations(decl, compute(toGens, lookup_func, evaluation_func/*, declares_func, supertypes_func, bounds_func*/));
	}
	
	println("cn: <cn>; decls: <size(decls)>; decls_raw: <size(decls_raw)>");
}

public void (AstNode) compute(ParameterizedEntity (Entity) toGens,
							  ParameterizedEntity (AstNode) lookup_func,
							  ParameterizedEntity (ParameterizedEntity) evaluation_func
							  /* 
							  set[ParameterizedEntity] (ParameterizedEntity) declares_func,
							  set[ParameterizedEntity] (ParameterizedEntity) supertypes_func,
							  set[Entity] (Entity) bounds_func
							  */) = void (AstNode t) {
							  
	 ParameterizedEntity val = lookup_func(t);
	 // println("<val>");
	 if(entity([ *_, anonymous(loc location, Entity declaredType) ]) := val.genericval) val = parameterizedentity(bindings([],[]), declaredType);
	 if( isMethodBinding(val.genericval) || isVariableBinding(val.genericval) || isFieldBinding(val.genericval) ) decls += val;
	 if(/ParameterizedEntity arg <- evaluation_func(val).bindings.args, arg == parameterizedentity(bindings([],[]), entity([]))) decls_raw += val;
	
	// println("lookup alpha of gens : <prettyprint(t)>-\><prettyprint(runStateTypeOf(lift(lift(lookup_a(lookup(toGenerics(mapper)))))(t))(t))>");
	// println("eval alpha of gens : <prettyprint(t)>-\><prettyprint(o(lift(lift(lookup_a(lookup(toGenerics(mapper)))))(t), lift(lift(eval_a(eval(toGenerics(mapper))))))(t))>");
	//println("lookup alpha plus gens: 
	//<prettyprint(
	/*
	v=
		runStateTypeOf(lookup_a_PlusGens(lookup_func, 
										 evaluation_func, 
										 parameterize(evaluation_func, bounds_func), 
										 parameterize(bounds_func, toGens, supertypes_func, declares_func),
										 parameterize_lookup(bounds_func, toGens, supertypes_func, declares_func),
										 filter_a(isParamDeclaredType(evaluation_func), evaluation_func),
										 filter_a(isGenericDecl(), evaluation_func))(t))(t);
	*/	
	/*								 
		cons = { <prettyprint(runSetTypeOf(c.lh)), prettyprint(runSetTypeOf(c.rh))> | c <-
		constraints(lookup_a_PlusGens(lookup_func, 
										 evaluation_func, 
										 parameterize(evaluation_func, bounds_func), 
										 parameterize(bounds_func, toGens, supertypes_func, declares_func),
										 parameterize_lookup(bounds_func, toGens, supertypes_func, declares_func),
										 filter_a(isParamDeclaredType(evaluation_func), evaluation_func),
										 filter_a(isGenericDecl(), evaluation_func)),									 
						lookup_a_PlusGens_Open(lookup_func, 
										 evaluation_func, 
										 parameterize(evaluation_func, bounds_func), 
										 parameterize(bounds_func, toGens, supertypes_func, declares_func),
										 parameterize_lookup(bounds_func, toGens, supertypes_func, declares_func),
										 filter_a(isParamDeclaredType(evaluation_func), evaluation_func),
										 filter_a(isGenericDecl(), evaluation_func)),
						filter_a(isGenericDecl(), evaluation_func), lift(eval_a(parameterize(evaluation_func, bounds_func))), lookup_func, evaluation_func, supertypes_func, bounds_func, toGens)(t) };
	*/
	  // for(c <- cons) println("constraint: <c>");
	//)>");
};

private void testComputations(AstNode body, void (AstNode) ccompute) {
	top-down visit(body) {
		case d:anonymousClassDeclaration(_): 
				{ for(decl<-d.bodyDeclarations) testComputations(decl, ccompute); return; }
		case d:annotationTypeDeclaration(_,_,_): 
				{ for(decl<-d.bodyDeclarations) testComputations(decl, ccompute); return; }
		case d:typeDeclaration(_,_,_,_,_,_,_): 
				{ for(decl<-d.bodyDeclarations) testComputations(decl, ccompute); return; }		
		case d:methodDeclaration(_,_,_,_,_,_, some(b)): { testComputations(b, ccompute); return; }
	
		case e:arrayAccess(_,_): ccompute(e); // arrayAccess(AstNode array, AstNode index)
		case e:arrayCreation(_,_,_): ccompute(e); // arrayCreation(AstNode type, list[AstNode] dimensions, Option[AstNode] initializer)
		case e:arrayInitializer(_): ccompute(e); // arrayInitializer(list[AstNode] expressions)
		case e:assignment(_,_): ccompute(e); // assignment(AstNode left, AstNode right)
		case e:booleanLiteral(_): ccompute(e); // _
		case e:castExpression(_,_): ccompute(e); // castExpression(AstNode type, AstNode expression)
		case e:characterLiteral(_): ccompute(e); // _
		case e:classInstanceCreation(_,_,_,_,_): ccompute(e); // classInstanceCreation(Option[AstNode] optionalExpression, AstNode type, list[AstNode] genericTypes, list[AstNode] typedArguments, Option[AstNode] anonymousClassDeclaration)
		case e:conditionalExpression(_,_,_): ccompute(e); // conditionalExpression(AstNode expression, AstNode thenBranch, AstNode elseBranch)
		case s:constructorInvocation(_,_): ccompute(s); // constructorInvocation(list[AstNode] genericTypes, list[AstNode] typedArguments)
		case e:fieldAccess(_,_): ccompute(e); // fieldAccess(AstNode expression, str name)
		case e:infixExpression(_,_,_,_): ccompute(e); // infixExpression(str operator, AstNode leftSide, AstNode rightSide, list[AstNode] extendedOperands)
		case e:instanceofExpression(_,_): ccompute(e); // instanceofExpression(AstNode left, AstNode right)
		case e:markerAnnotation(_): ccompute(e); // _
		case e:methodInvocation(_,_,_,_): ccompute(e); // methodInvocation(Option[AstNode] optionalExpression, list[AstNode] genericTypes, str name, list[AstNode] typedArguments)
		case e:normalAnnotation(_,_): ccompute(e); // _
		case e:nullLiteral(): ccompute(e); // _
		case e:parenthesizedExpression(_): ccompute(e); // _
		case e:postfixExpression(_,_): ccompute(e); // postfixExpression(AstNode operand, str operator)
		case e:prefixExpression(_,_): ccompute(e); // prefixExpression(AstNode operand, str operator)
		case e:qualifiedName(_,_): if("typeBinding" in e@bindings) ccompute(e); // qualifiedName(AstNode qualifier, str name)
		
		case e:simpleName(_): if("typeBinding" in e@bindings) ccompute(e); // _
		
		case e:singleMemberAnnotation(_,_): ccompute(e); // _
		case e:stringLiteral(_): ccompute(e); // _
		
		case s:superConstructorInvocation(_,_,_): ccompute(s); // superConstructorInvocation(Option[AstNode] optionalExpression, list[AstNode] genericTypes, list[AstNode] typedArguments)
		
		case e:superFieldAccess(_,_): ccompute(e); // superFieldAccess(Option[AstNode] optionalQualifier, str name)
		case e:superMethodInvocation(_,_,_,_): ccompute(e); // superMethodInvocation(Option[AstNode] optionalQualifier, list[AstNode] genericTypes, str name, list[AstNode] typedArguments)
		case e:thisExpression(_): ccompute(e); // _
		case e:typeLiteral(_): ccompute(e); // _
		case e:variableDeclarationExpression(_,_,_): ccompute(e); // variableDeclarationExpression(_, AstNode type, list[AstNode] fragments)
		
		case d:singleVariableDeclaration(_,_,_,_,_): ccompute(d);
		case d:variableDeclarationFragment(_,_): ccompute(d);
	}
}

private set[ParameterizedEntity] decls = {};
private set[ParameterizedEntity] decls_raw = {};

