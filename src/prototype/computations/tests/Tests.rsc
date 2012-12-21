@license{
  Copyright (c) 2009-2011 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - A.Izmaylova@cwi.nl}
module prototype::computations::tests::Tests

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::JDT;
import prototype::lang::java::jdt::refactorings::Java;
import prototype::lang::java::jdt::refactorings::JavaADT;
import prototype::lang::java::jdt::refactorings::JavaADTVisitor;
import prototype::lang::java::jdt::refactorings::JDT4Refactorings;
import prototype::lang::java::jdt::refactorings::PrettyPrintUtil;
import prototype::lang::java::jdt::refactorings::ValuesUtil;

import prototype::computations::tests::TestProjects;

import prototype::computations::mksubsts::ConstraintComputation;
import prototype::computations::mksubsts::ConstraintInference;
import prototype::computations::mksubsts::LanguageInterface;
import prototype::computations::mksubsts::Monads;
import prototype::computations::mksubsts::TypeComputation;
import prototype::computations::mksubsts::FunctionsOfTypeValues;

import Prelude;


public void main1() { 
	testConstraintSemantics(eclipseSources); 
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
		for(str cs <- { prettyprint(c) | Constraint[SubstsT[Entity]] c <- cons })
			print1 = print1 + cs + "\n";
		tracer(true, "Constraints <print1>");		

		str print2 = "";
		for(str cs <- { prettyprint(c) | Constraint[SubstsT[Entity]] c <- cls})
			print2 = print2 + cs + "\n";
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