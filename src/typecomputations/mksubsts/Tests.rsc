module typecomputations::mksubsts::Tests

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::JDT;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;
import lang::java::jdt::refactorings::JavaADTVisitor;
import lang::java::jdt::refactorings::JDT4Refactorings;
import lang::java::jdt::refactorings::PrettyPrintUtil;
import lang::java::jdt::refactorings::ValuesUtil;

import typecomputations::tests::TestProjects;

import typecomputations::mksubsts::ConstraintComputatation;
import typecomputations::mksubsts::LanguageInterface;
import typecomputations::mksubsts::SubstitutionMonad;
import typecomputations::mksubsts::TypeComputation;
import typecomputations::mksubsts::TypeValuesFuncs;

import Prelude;


public void main1() { 
	testConstraintSemantics(testcase5); 
}

public void testComputations(list[loc] projects) { for(project <- projects) testComputations(project); }
private void testComputations(loc project) {
	println("calculating facts and asts...");
	set[AstNode] compilationUnits = createAstsFromProjectR(project); 
	println("done...");
	int cn = 0;
	for(AstNode cu <- compilationUnits) {
		cn += 1;
		println(cu@location);
		
		CompilUnit facts = cu@typeComputationModel;
		Mapper mapper = cu@semanticsOfParameterizedTypes;
		
		 println("facts: <facts>"); println("mapper: <mapper>");
		
		for(decl <- cu.typeDeclarations) 
			testComputations(decl, compute(facts, mapper));
	}
	
	println("cn: <cn>");
}

public void testConstraintSemantics(list[loc] projects) { for(project <- projects) testConstraintSemantics(project); }
private void testConstraintSemantics(loc project) {
	println("calculating facts and asts...");
	set[AstNode] compilationUnits = createAstsFromProjectR(project); 
	println("done...");
	for(AstNode cu <- compilationUnits) {
		println(cu@location);
		
		CompilUnit facts = cu@typeComputationModel;
		Mapper mapper = cu@semanticsOfParameterizedTypes;
		
		set[Constraint[SubstsT[Entity]]] cons = {};
		
		(AstNode (AstNode) (AstNode (AstNode) super) {
			return AstNode (AstNode n) {
				cons += constrain(n, facts, mapper);
				return super(n);
			};
		} o visitADT)(cu);
		
		set[Constraint[SubstsT[Entity]]] cls = { *inferTAs(facts, mapper, c) | Constraint[SubstsT[Entity]] c <- cons };
		
		str print1 = "";
		//for(Constraint[SubstsT[Entity]] c <- cons)
		//	print1 = print1 + prettyprint(c) + "\n";
		//tracer(true, "Constraints <print1>");		

		str print2 = "";
		for(Constraint[SubstsT[Entity]] c <- cls)
			print2 = print2 + prettyprint(c) + "\n";
		tracer(true, "Constraints (closure) <print2>");		
	}	
}

public void testLookupSemantics(list[loc] projects) { for(project <- projects) testLookupSemantics(project); }
private void testLookupSemantics(loc project) {
	println("calculating facts and asts...");
	set[AstNode] compilationUnits = createAstsFromProjectR(project); 
	println("done...");
	for(AstNode cu <- compilationUnits) {
		println(cu@location);
		
		CompilUnit facts = cu@typeComputationModel;
		Mapper mapper = cu@semanticsOfParameterizedTypes;
		
		(AstNode (AstNode) (AstNode (AstNode) super) {
			return AstNode (AstNode n) {
				if(methodInvocation(Option[AstNode] optionalExpression,_,_,_) := n) {
					println(prettyprint(n));
					SubstsT[Entity] tn = glookupc(facts, mapper, n);
					TypeOf[tuple[Entity, Substs]] v = run(tn)(substs([],[]));
					/*if(v.v[1] != substs([],[]))*/ println("substs: <prettyprint(v.v[1])>");
				}
				return super(n);
			};
		} o visitADT)(cu);
	}	
}

public void testEvalSemantics(list[loc] projects) { for(project <- projects) testEvalSemantics(project); }
private void testEvalSemantics(loc project) {
	println("calculating facts and asts...");
	set[AstNode] compilationUnits = createAstsFromProjectR(project); 
	println("done...");
	for(AstNode cu <- compilationUnits) {
		println(cu@location);
		
		CompilUnit facts = cu@typeComputationModel;
		Mapper mapper = cu@semanticsOfParameterizedTypes;
		
		(AstNode (AstNode) (AstNode (AstNode) super) {
			return AstNode (AstNode n) {
				if(methodInvocation(Option[AstNode] optionalExpression,_,_,_) := n) {
					SubstsT[Entity] tn = gevalc(mapper, lookup(n));
					if(some(AstNode oe) := optionalExpression) {
						SubstsT[Entity] toe = gevalc(mapper, lookup(oe));
						TypeOf[tuple[Entity, Substs]] soe = run(toe)(substs([],[]));
						if(soe.v[1] != substs([],[])) {
							println(prettyprint(lookup(oe)));
							println(prettyprint(soe.v[1]));
						}
					}
					TypeOf[Entity, Substs] sn = run(tn)(substs([],[]));
					if(sn.v[1] != substs([],[])) {
						println(prettyprint(lookup(n)));
						println(prettyprint(sn.v[1]));
					}
				}
				return super(n);
			};
		} o visitADT)(cu);
	}	
}

public void testSupertypesSemantics(list[loc] projects) { for(project <- projects) testSupertypesSemantics(project); }
private void testSupertypesSemantics(loc project) {
	println("calculating facts and asts...");
	set[AstNode] compilationUnits = createAstsFromProjectR(project); 
	println("done...");
	for(AstNode cu <- compilationUnits) {

		println(cu@location);
		
		CompilUnit facts = cu@typeComputationModel;
		Mapper mapper = cu@semanticsOfParameterizedTypes;
		
		(AstNode (AstNode) (AstNode (AstNode) super) {
			return AstNode (AstNode n) {
				if(methodInvocation(Option[AstNode] optionalExpression,_,_,_) := n) {
					// println(prettyprint(n));
					Entity dtype = eval(decl(lookup(n)));
					Entity t = zero();
					SubstsT_[bool] sups = returnS_(false);
					if(some(AstNode oe) := optionalExpression) {
						t = getType(oe);
						sups = supertypec_(facts, mapper, <t, dtype>);
					} else {
						t = n@scope;
						sups = supertypec_(facts, mapper, <t, dtype>);
					}
					list[tuple[bool, Substs]] s = run(sups)(substs([],[]));
						for(<bool b, Substs s_> <- s, s_ != substs([],[])) {
							println(prettyprint(lookup(n)));
							println(prettyprint(t));
							println("supertypes: <b> --- <prettyprint(s_)>");
						}
				}
				return super(n);
			};
		} o visitADT)(cu);
	}	
}

public void (AstNode) compute(CompilUnit facts, Mapper mapper) 
	= void (AstNode t) {
		/* tracer: */ tracer(true, "term: <prettyprint(t)>");
		// println("Type computations: <prettyprint(execute(facts, mapper, t, bindinj(liftM(t), glookup)))>");	
		ConsM[Constraint[M[PEntity]]] cons = cconstrain(inj(t));
		set[MId[tuple[Constraint[M[PEntity]], AstNode]]] cons1 = execute(facts, mapper, t, cons);
		set[tuple[Constraint[str], str]] cons2 = {};
		set[MId[Constraint[PEntity]]] conscls = {};
		for(MId[tuple[Constraint[M[PEntity]], AstNode]] c <-  cons1)
			visit(c) { 
				case <eq(M[PEntity] val1, M[PEntity] val2), AstNode tt>: {
					set[TypeOf[tuple[PEntity, AstNode]]] val11 = execute(facts, mapper, tt, val1);
					set[TypeOf[tuple[PEntity, AstNode]]] val22 = execute(facts, mapper, tt, val2);
					lh = getOneFrom(val11).val; rh = getOneFrom(val22).val;
					conscls += closure(facts, mapper, lh[1], rh[1], eq(lh[0], rh[0]));
					// cons2 += { <eq(prettyrint(val11), prettyprint(val22)), "t"> };
				}
				case <subtype(M[PEntity] val1, M[PEntity] val2), AstNode tt>: { 
					set[TypeOf[tuple[PEntity, AstNode]]] val11 = execute(facts, mapper, tt, val1);
					set[TypeOf[tuple[PEntity, AstNode]]] val22 = execute(facts, mapper, tt, val2);
					lh = getOneFrom(val11).val; rh = getOneFrom(val22).val;
					conscls += closure(facts, mapper, lh[1], rh[1], subtype(lh[0], rh[0]));
					// cons2 += { <eq(prettyrint(val11), prettyprint(val22)), "t"> };
				}
			}
		println("Constraints computations: <{ prettyprint(c.val) | MId[Constraint[PEntity]] c <- conscls }>");
								  
	};

private void testComputations(AstNode body, void (AstNode) f) {
	top-down visit(body) {
		case d:anonymousClassDeclaration(_): 
				{ for(decl<-d.bodyDeclarations) testComputations(decl, f); return; }
		case d:annotationTypeDeclaration(_,_,_): 
				{ for(decl<-d.bodyDeclarations) testComputations(decl, f); return; }
		case d:typeDeclaration(_,_,_,_,_,_,_): 
				{ for(decl<-d.bodyDeclarations) testComputations(decl, f); return; }		
		case d:methodDeclaration(_,_,_,_,_,_, some(b)): { testComputations(b, f); return; }
		case e:arrayAccess(_,_): f(e); 
		case e:arrayCreation(_,_,_): f(e);  
		case e:arrayInitializer(_): f(e);  
		case e:assignment(_,_): f(e);  
		case e:booleanLiteral(_): f(e); 
		case e:castExpression(_,_): f(e);  
		case e:characterLiteral(_): f(e); 
		case e:classInstanceCreation(_,_,_,_,_): f(e);  
		case e:conditionalExpression(_,_,_): f(e);  
		case s:constructorInvocation(_,_): f(s);  
		case e:fieldAccess(_,_): f(e); 
		case e:infixExpression(_,_,_,_): f(e);  
		case e:instanceofExpression(_,_): f(e); 
		case e:markerAnnotation(_): f(e); 
		case e:methodInvocation(_,_,_,_): f(e); 
		case e:normalAnnotation(_,_): f(e); 
		case e:nullLiteral(): f(e); 
		case e:parenthesizedExpression(_): f(e); 
		case e:postfixExpression(_,_): f(e); 
		case e:prefixExpression(_,_): f(e); 
		case e:qualifiedName(_,_): if("typeBinding" in e@bindings) f(e); 
		case e:simpleName(_): if("typeBinding" in e@bindings) f(e); 
		case e:singleMemberAnnotation(_,_): f(e);
		case e:stringLiteral(_): f(e);
		case s:superConstructorInvocation(_,_,_): f(s); 
		case e:superFieldAccess(_,_): f(e); 
		case e:superMethodInvocation(_,_,_,_): f(e);  
		case e:thisExpression(_): f(e); 
		case e:typeLiteral(_): f(e); 
		case e:variableDeclarationExpression(_,_,_): f(e); 
		case d:singleVariableDeclaration(_,_,_,_,_): f(d);
		case d:variableDeclarationFragment(_,_): f(d);
	}
}
/*
- arrayAccess(AstNode array, AstNode index);
- arrayCreation(AstNode type, list[AstNode] dimensions, Option[AstNode] initializer);
- arrayInitializer(list[AstNode] expressions);
- assignment(AstNode left, AstNode right);
- castExpression(AstNode type, AstNode expression);
- classInstanceCreation(Option[AstNode] optionalExpression, AstNode type, list[AstNode] genericTypes, list[AstNode] typedArguments, Option[AstNode] anonymousClassDeclaration);
- conditionalExpression(AstNode expression, AstNode thenBranch, AstNode elseBranch);
- constructorInvocation(list[AstNode] genericTypes, list[AstNode] typedArguments);
- fieldAccess(AstNode expression, str name);
- infixExpression(str operator, AstNode leftSide, AstNode rightSide, list[AstNode] extendedOperands);
- instanceofExpression(AstNode left, AstNode right);
- methodInvocation(Option[AstNode] optionalExpression, list[AstNode] genericTypes, str name, list[AstNode] typedArguments);
- postfixExpression(AstNode operand, str operator);
- prefixExpression(AstNode operand, str operator);
- qualifiedName(AstNode qualifier, str name);
- superConstructorInvocation(Option[AstNode] optionalExpression, list[AstNode] genericTypes, list[AstNode] typedArguments);
- superFieldAccess(Option[AstNode] optionalQualifier, str name);
- superMethodInvocation(Option[AstNode] optionalQualifier, list[AstNode] genericTypes, str name, list[AstNode] typedArguments);
- variableDeclarationExpression(_, AstNode type, list[AstNode] fragments);
*/
