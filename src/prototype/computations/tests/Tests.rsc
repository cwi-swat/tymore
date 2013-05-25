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
import prototype::computations::mksubsts::AbstractConstraintSolver;

import Prelude;


public void testit() { 
	testConstraintSemantics(testcases); 
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
		
		//(AstNode (AstNode) (AstNode (AstNode) super) {
		//	return AstNode (AstNode n) {
		//		cons += constrain(n, facts, mapper);
		//		return super(n);
		//	};
		//} o visitADT)(cu);
		
		top-down visit(cu) {
			case AstNode n: { cons += constrain(n, facts, mapper); insert n; }
		}
		
		set[Constraint[SubstsT[Entity]]] cls = { *inferTypeArguments(facts, mapper, c) | Constraint[SubstsT[Entity]] c <- cons };
		
		//str print1 = "";
		//for(str cs <- { prettyprint(c) | Constraint[SubstsT[Entity]] c <- cons })
		//	print1 = print1 + cs + "\n";
		//tracer(true, "Constraints: \n <print1>");		

		str print2 = "";
		for(str cs <- { prettyprint(c) | Constraint[SubstsT[Entity]] c <- cls})
			print2 = print2 + cs + "\n";
		tracer(true, "Constraints (closure): \n <print2>");		
		
		set[Constraint[SubstsTL[Entity]]] cls_ = { (Constraint::subtype(lh,rh) := c) ? Constraint::subtype(tauToSubstsTL(lh), tauToSubstsTL(rh)) 
																					  : Constraint::eq(tauToSubstsTL(c.lh), tauToSubstsTL(c.rh)) 
																			| Constraint[SubstsT[Entity]] c <- cls };
										
		set[Constraint[SubstsTL[Entity]]] clsSolved = {};
		solve(solutions) {
			clsSolved = { *solveit(facts, mapper, c) | Constraint[SubstsTL[Entity]] c <- cls_ };
		}
		
	}	
	tracer(true, "Solutions: <for(s<-solutions){><prettyprint(s)> = <prettyprint(solutions[s])> \n <}>");
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
		
		//(AstNode (AstNode) (AstNode (AstNode) super) {
		//	return AstNode (AstNode n) {
		//		if(methodInvocation(Option[AstNode] optionalExpression,_,_,_) := n) {
		//			SubstsT[Entity] tn = glookupc(facts, mapper, n);
		//			TypeOf[tuple[Entity, Substs]] v = run(tn)(substs([],[]));
		//			if(v.v[1] != substs([],[])) {
		//				println(prettyprint(n));
		//				println("substs: <prettyprint(v.v[1])>");
		//			}
		//		}
		//		return super(n);
		//	};
		//} o visitADT)(cu);
		
		top-down visit(cu) {
			case AstNode n: { 
				if(methodInvocation(Option[AstNode] optionalExpression,_,_,_) := n) {
					SubstsT[Entity] tn = glookupc(facts, mapper, n);
					TypeOf[tuple[Entity, Substs]] v = run(tn)(substs([],[]));
					if(v.v[1] != substs([],[])) {
						println(prettyprint(n));
						println("substs: <prettyprint(v.v[1])>");
					}
				}
				insert n; 
			}
		}
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
		
		//(AstNode (AstNode) (AstNode (AstNode) super) {
		//	return AstNode (AstNode n) {
		//		if(methodInvocation(Option[AstNode] optionalExpression,_,_,_) := n) {
		//			SubstsT[Entity] tn = gevalc(mapper, lookup(n));
		//			if(some(AstNode oe) := optionalExpression) {
		//				SubstsT[Entity] toe = gevalc(mapper, lookup(oe));
		//				TypeOf[tuple[Entity, Substs]] soe = run(toe)(substs([],[]));
		//				if(soe.v[1] != substs([],[])) {
		//					println(prettyprint(lookup(oe)));
		//					println(prettyprint(soe.v[1]));
		//				}
		//			}
		//			TypeOf[Entity, Substs] sn = run(tn)(substs([],[]));
		//			if(sn.v[1] != substs([],[])) {
		//				println(prettyprint(lookup(n)));
		//				println(prettyprint(sn.v[1]));
		//			}
		//		}
		//		return super(n);
		//	};
		//} o visitADT)(cu);
		
		top-down visit(cu) {
			case AstNode n: {
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
				insert n;
			}
		}
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
		
		//(AstNode (AstNode) (AstNode (AstNode) super) {
		//	return AstNode (AstNode n) {
		//		if(methodInvocation(Option[AstNode] optionalExpression,_,_,_) := n) {
		//			Entity dtype = eval(decl(lookup(n)));
		//			list[Entity] t = [];
		//			SubstsT_[bool] sups = returnS_(false);
		//			if(some(AstNode oe) := optionalExpression) t = [ getType(oe) ];
		//			else t = n@scopes;
		//			if(size(t) > 1) println("NESTING : ");
		//			for(Entity tt <- t) {
		//				sups = supertypec_(facts, mapper, <tt, dtype>);
		//				list[tuple[bool, Substs]] s = run(sups)(substs([],[]));
		//				list[bool] ss = supertype(facts, mapper, <tt, dtype>);
		//				for(<bool b, Substs s_> <- s, s_ != substs([],[]) ) {
		//					println("supertype : <ss>");
		//					println("supertypec_ : ");
		//					println(prettyprint(n));
		//					println(prettyprint(eval(decl(lookup(n)))));
		//					println(prettyprint(tt));
		//					println("supertypes: <b> --- <prettyprint(s_)>");
		//				}
		//			}
		//		}
		//		return super(n);
		//	};
		//} o visitADT)(cu);
		
		top-down visit(cu) {
			case AstNode n: {
				if(methodInvocation(Option[AstNode] optionalExpression,_,_,_) := n) {
					Entity dtype = eval(decl(lookup(n)));
					list[Entity] t = [];
					SubstsT_[bool] sups = returnS_(false);
					if(some(AstNode oe) := optionalExpression) t = [ getType(oe) ];
					else t = n@scopes;
					if(size(t) > 1) println("NESTING : ");
					for(Entity tt <- t) {
						sups = supertypec_(facts, mapper, <tt, dtype>);
						list[tuple[bool, Substs]] s = run(sups)(substs([],[]));
						list[bool] ss = supertype(facts, mapper, <tt, dtype>);
						for(<bool b, Substs s_> <- s, s_ != substs([],[]) ) {
							println("supertype : <ss>");
							println("supertypec_ : ");
							println(prettyprint(n));
							println(prettyprint(eval(decl(lookup(n)))));
							println(prettyprint(tt));
							println("supertypes: <b> --- <prettyprint(s_)>");
						}
					}
				}
				insert n;
			}
		}
	}	
}