module typecomputations::Constraints

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;
import lang::java::jdt::refactorings::PrettyPrintUtil;
import lang::java::jdt::refactorings::ValuesUtil;

import typecomputations::TypeValues;
import typecomputations::TypeValuesPlusGens;
import typecomputations::SemanticDomains;
import typecomputations::TypeMonadTransformers;
import typecomputations::TypeComputations;
import typecomputations::ConstraintMonadTransformers;

import Prelude;


alias Mon = M[PEntity];
	
public set[MId[Constraint[Mon]]] constrain(t:arrayAccess(_,_)) 
	= {};	
public set[MId[Constraint[Mon]]] constrain(t:arrayCreation(_, list[AstNode] _, some(AstNode initializer))) 
	= { inclMId(subtype(glookup(inj(rmvParentheses(initializer))), glookup(inj(t)))) }
	;	
public set[MId[Constraint[Mon]]] constrain(t:arrayInitializer(list[AstNode] exprs)) 
	= { inclMId(subtype(glookup(inj(rmvParentheses(expr))), glookup(inj(t)))) | expr <- exprs }
	;	
public set[MId[Constraint[Mon]]] constrain(t:assignment(AstNode _, nullLiteral())) 
	= {};
public set[MId[Constraint[Mon]]] constrain(t:assignment(AstNode lt, AstNode rt)) 
	= { inclMId(subtype(glookup(inj(rmvParentheses(rt))), glookup(inj(rmvParentheses(lt))))) }
	;
public set[MId[Constraint[Mon]]] constrain(CompilUnit facts, Mapper mapper, t:castExpression(_, AstNode e)) 
	= { (isDownCast(facts, mapper, t)) ? inclMId(subtype(glookup(inj(t)), glookup(inj(rmvParentheses(e))))) 
									   : inclMId(subtype(glookup(inj(rmvParentheses(e))), glookup(inj(t)))) }
	;
public set[MId[Constraint[Mon]]] constrain(t:classInstanceCreation(none(),_, [], [],_)) 
	= {};
public set[MId[Constraint[Mon]]] constrain(t:classInstanceCreation(none(),_, [], list[AstNode] args,_)) 
	= { inclMId(subtype(glookup(inj(rmvParentheses(args[i]))), bind(glookup(inj(t)), gparam(inj(i))))) | int i <- [0..size(args) - 1], args[i] != nullLiteral() }
	;
public set[MId[Constraint[Mon]]] constrain(t:classInstanceCreation(some(AstNode e),_, [], list[AstNode] args, none())) {
	if(isEmpty(args)) return {};
	return  { inclMId(subtype(glookup(inj(rmvParentheses(args[i]))), bind(glookup(inj(t)), gparam(inj(i))))) | int i <- [0..size(args) - 1], args[i] != nullLiteral() } 
		  + { inclMId(subtype(glookup(inj(rmvParentheses(e))), bindinj(glookup(inj(t)), gdecl))) };
}	
public set[MId[Constraint[Mon]]] constrain(t:classInstanceCreation(_,_, [], list[AstNode] args, some(AstNode anonym))) 
	= {};
public set[MId[Constraint[Mon]]] constrain(t:conditionalExpression(AstNode _, AstNode thenBranch, AstNode elseBranch)) 
	=   { inclMId(subtype(glookup(inj(t)), glookup(inj(rmvParentheses(thenBranch))))) }
	  + { inclMId(subtype(glookup(inj(t)), glookup(inj(rmvParentheses(elseBranch))))) }
	;
public set[MId[Constraint[Mon]]] constrain(t:constructorInvocation(_, list[AstNode] args)) {
	if(isEmpty(args)) return {};
	return { inclMId(subtype(glookup(inj(rmvParentheses(args[i]))), bind(glookup(inj(t)), gparam(inj(i))))) | int i <- [0..size(args) - 1], args[i] != nullLiteral() };
}
public set[MId[Constraint[Mon]]] constrain(t:fieldAccess(AstNode e,_)) 
	= { inclMId(eq(glookup(inj(rmvParentheses(e))), bindinj(glookup(inj(t)), gdecl))) }
	;
public set[MId[Constraint[Mon]]] constrain(t:methodInvocation(none(),_,_, list[AstNode] args)) {
	if(isEmpty(args)) return {};
	return { inclMId(subtype(glookup(inj(rmvParentheses(args[i]))), bind(glookup(inj(t)), gparam(inj(i))))) | int i <- [0..size(args) - 1], args[i] != nullLiteral() };
}
public set[MId[Constraint[Mon]]] constrain(t:methodInvocation(some(AstNode e),_,_, list[AstNode] args)) { 
	set[MId[Constraint[Mon]]] cons = { inclMId(subtype(glookup(inj(rmvParentheses(e))), bindinj(glookup(inj(t)), gdecl))) };
	if(isEmpty(args)) return cons; 
	set[MId[Constraint[Mon]]] cons1 = { inclMId(subtype(glookup(inj(rmvParentheses(args[i]))), bind(glookup(inj(t)), gparam(inj(i))))) | int i <- [0..size(args) - 1], args[i] != nullLiteral() };
	return cons + cons1;
}
public set[MId[Constraint[Mon]]] constrain(t:qualifiedName(_,_)) 
	= {};
public set[MId[Constraint[Mon]]] constrain(t:superConstructorInvocation(some(AstNode e), _, list[AstNode] args)) {
	set[MId[Constraint[Mon]]] cons = { inclMId(subtype(glookup(inj(rmvParentheses(e))), bindinj(glookup(inj(t)), gdecl))) };
	if(isEmpty(args)) return cons;
	set[MId[Constraint[Mon]]] cons1 = { inclMId(subtype(glookup(inj(rmvParentheses(args[i]))), bind(glookup(inj(t)), gparam(inj(i))))) | int i <- [0..size(args) - 1], args[i] != nullLiteral() };
	return cons + cons1;
}
public set[MId[Constraint[Mon]]] constrain(t:superFieldAccess(_,_)) 
	= {};
public set[MId[Constraint[Mon]]] constrain(t:superMethodInvocation(_,_,_, list[AstNode] args)) {
	if(isEmpty(args)) return {};
	return { inclMId(subtype(glookup(inj(rmvParentheses(args[i]))), bind(glookup(inj(t)), gparam(inj(i))))) | int i <- [0..size(args) - 1], args[i] != nullLiteral() };
}
public set[MId[Constraint[Mon]]] constrain(t:singleVariableDeclaration(str name,_,_, some(nullLiteral()),_)) 
	= {};
public set[MId[Constraint[Mon]]] constrain(t:singleVariableDeclaration(str name,_,_, some(AstNode initializer),_)) 
	= { inclMId(subtype(glookup(inj(rmvParentheses(initializer))), glookup(inj(setAnnotations(simpleName(name), getAnnotations(t)))))) }
	;
public set[MId[Constraint[Mon]]] constrain(t:variableDeclarationFragment(str name, some(nullLiteral()))) 
	= {};
public set[MId[Constraint[Mon]]] constrain(t:variableDeclarationFragment(str name, some(AstNode initializer))) 
	= { inclMId(subtype(glookup(inj(rmvParentheses(initializer))), glookup(inj(setAnnotations(simpleName(name), getAnnotations(t)))))) }
	;
public default set[MId[Constraint[Mon]]] constrain(AstNode t) = {};
public default set[MId[Constraint[Mon]]] constrain(CompilUnit facts, Mapper mapper, AstNode t) = {};
/*
@doc{ the basic lookup semantics over type values }
public Entity lookup(e:arrayAccess(_,_)); 
public Entity lookup(e:arrayCreation(AstNode dtype, list[AstNode] _, Option[AstNode] initializer)); 
public Entity lookup(e:arrayInitializer(list[AstNode] expressions)); 
public Entity lookup(e:assignment(AstNode le,_));
public Entity lookup(e:castExpression(_,_)); // TODO: isDownCast
public Entity lookup(e:classInstanceCreation(_,_,_,_,_)); // TODO: param and decl computations
public Entity lookup(e:conditionalExpression(_,_,_)); // TODO 
public Entity lookup(s:constructorInvocation(_,_));
public Entity lookup(e:fieldAccess(_,_)); 
public Entity lookup(e:methodInvocation(_,_,_,_)); 
public Entity lookup(e:qualifiedName(_,_));  
public Entity lookup(s:superConstructorInvocation(_,_,_)); // TODO 
public Entity lookup(e:superFieldAccess(_,_)); // TODO 
public Entity lookup(e:superMethodInvocation(_,_,_,_)); // TODO 
public Entity lookup(e:variableDeclarationExpression(_,_,_)); // TODO 

public Entity lookup(d:anonymousClassDeclaration(_)); // TODO
public Entity lookup(d:typeDeclaration(_,_,_,_,_,_,_));
public Entity lookup(d:methodDeclaration(_,_,_,_,_,_,_)) ;
public default Entity lookup(AstNode t) { throw "No lookup function defined for a term <t> !"; }
*/

public set[MId[Constraint[PEntity]]] closure(CompilUnit facts, Mapper mapper, AstNode lht, AstNode rht, Constraint[PEntity] constraint) {
	/* tracer: */ tracer(true, "closure: original constraint <prettyprint(constraint)>");
	set[MId[Constraint[PEntity]]] cons = {};
	PEntity lh = pzero();
	PEntity rh = pzero();
	bool isEq = false;
	switch(constraint) {
		case eq(PEntity val1, PEntity val2): { isEq = true; lh = val1; rh = val2; }
		case subtype(PEntity val1, PEntity val2): { lh = val1; rh = val2; }
	};
	// temporarily solution, has to be in a proper monadic style
	PEntity lhtype = getOneFrom(execute(facts, mapper, lht, geval(inj(lh)))).val[0];
	PEntity rhtype = getOneFrom(execute(facts, mapper, rht, geval(inj(rh)))).val[0];
	if(isArrayOrPrimitiveType(lhtype.genval) || isArrayOrPrimitiveType(rhtype.genval)) { 
		assert(lhtype.genval == rhtype.genval); 
		tracer(false, "closure: array or primitive types"); 
		return cons; 
	}
	// handling the cases where the type constains variables in its substitution
	if(lh == lhtype) lh = tpbound(mapper, lh);
	if(rh == rhtype) rh = tpbound(mapper, rh);
	lhtype = tpbound(mapper, lhtype);
	rhtype = tpbound(mapper, rhtype);
	if(isArrayOrPrimitiveType(lhtype.genval) && isArrayOrPrimitiveType(rhtype.genval)) { 
		assert(lhtype.genval == rhtype.genval); 
		tracer(false, "closure: array or primitive types"); 
		return cons; 
	}
	if(isTypeArgument(lhtype.genval) || isTypeArgument(rhtype.genval)) 
		/* in general case: _type -> liftM(typeof(<_type, _t>)) */
		cons = cons + { (isEq) ? inclMId(eq((isTypeArgument(lhtype)) ? getGenericVal(lhtype) : lhtype, 
											(isTypeArgument(rhtype)) ? getGenericVal(rhtype) : rhtype)) 
				   		   	   : inclMId(subtype((isTypeArgument(lhtype)) ? getGenericVal(lhtype) : lhtype, 
				   		   	   					 (isTypeArgument(rhtype)) ? getGenericVal(rhtype) : rhtype)) };
	lhtype = bound(mapper, lhtype);
	rhtype = bound(mapper, rhtype);
	list[Entity] lhtypeparams = getTypeParamsOrArgs(lhtype.genval);
	list[Entity] rhtypeparams = getTypeParamsOrArgs(rhtype.genval);
	if(isEmpty(lhtypeparams) && isEmpty(rhtypeparams)) return cons;
	if(isEq || (lhtype.genval == rhtype.genval) || (!isEmpty(lhtypeparams) && isEmpty(rhtypeparams))) { 
		tracer(false, "<prettyprint(lhtype)> ; <prettyprint(rhtype)>");
		if(lhtype.genval != rhtype.genval) {
			// attempt of equalizing types to propagate type arguments
			/* tracer: */ tracer(true, "equalizing: <prettyprint(lh)> <prettyprint(rh)>");
			if(!isEmpty(lhtypeparams) && isEmpty(rhtypeparams)) { 
				return cons + closureEq(facts, mapper, lht, rht, eq(lhtype, pentity(bindings([ typeArgument(pzero(), param, rh.genval, mapper) | param <- lhtypeparams ], 
														  							 		 lhtypeparams), 
												 			 		lhtype.genval)[@paramval = lhtype@paramval]));
			} elseif (isEmpty(lhtypeparams) && !isEmpty(rhtypeparams)) {
				return cons + closureEq(facts, mapper, lht, rht, eq(pentity(bindings([ typeArgument(pzero(), param, lh.genval, mapper) | param <- rhtypeparams ], 
														  							  rhtypeparams), 
												 			 		rhtype.genval)[@paramval = rhtype@paramval], rhtype));
			} if(!isEmpty(lhtypeparams) && !isEmpty(rhtypeparams)) {
				throw "closure: equality breaks on generic types";
			} else {
				return cons;
			}
		} 
		return cons + closureEq(facts, mapper, lht, rht, eq(lhtype, rhtype));
	}
	tracer(true, "lh: <prettyprint(lhtype)>; lh paramval: <prettyprint(lhtype@paramval)> ; rh: <prettyprint(rhtype)>");
	set[PEntity] sups = supertypesAll(facts, mapper, lhtype);
	/* tracer: */ tracer(true, "<{ prettyprint(sup) | PEntity sup <- sups }>");
	lhtype = if(sup <- sups && (sup.genval == rhtype.genval)) sup;
	return cons + closureEq(facts, mapper, lht, rht, eq(lhtype, rhtype));
}
private set[MId[Constraint[PEntity]]] closureEq(CompilUnit facts, Mapper mapper, AstNode lht, AstNode rht, eq(PEntity lh, PEntity rh)) {
	/* tracer: */ tracer(false, "closureEq: lh: <prettyprint(lh)>; rh: <prettyprint(rh)>");
	list[Entity] params = getTypeParamsOrArgs(lh.genval);
	if(isEmpty(params)) return {};
	// remark1: pentity(lh.bindings, param) and pentity(rh.bindings, param) are ok without @paramval because tpbound does not require it
	// remark2: it is essential that tpbound is called here
	return { *closure(facts, mapper, lht, rht, eq(tpbound(mapper, pentity(lh.bindings, param)), tpbound(mapper, pentity(rh.bindings, param))))
				| Entity param <- params };
}