module typecomputations::mksubsts::Constraints

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;
import lang::java::jdt::refactorings::PrettyPrintUtil;
import lang::java::jdt::refactorings::ValuesUtil;

import typecomputations::TypeValues;
import typecomputations::mksubsts::TypeComputations;

import Prelude;


public data Constraint[&M] = eq(&M lh, &M rh)
					  		 | subtype(&M lh, &M rh)
					  		 | czero();

public set[Constraint[BLogger[Entity]]] constrain(t:arrayAccess(_,_), CompilUnit facts, Mapper mapper) 
	= {};	
public set[Constraint[BLogger[Entity]]] constrain(t:arrayCreation(_, list[AstNode] _, some(AstNode initializer)), CompilUnit facts, Mapper mapper) 
	= { subtype(lookup_(facts, mapper, rmv(initializer)), lookup_(facts, mapper, t)) }
	;	
public set[Constraint[BLogger[Entity]]] constrain(t:arrayInitializer(list[AstNode] exprs), CompilUnit facts, Mapper mapper) 
	= { subtype(lookup_(facts, mapper, rmv(expr)), lookup_(facts, mapper, t)) | expr <- exprs }
	;	
public set[Constraint[BLogger[Entity]]] constrain(t:assignment(AstNode _, nullLiteral()), CompilUnit facts, Mapper mapper) 
	= {};
public set[Constraint[BLogger[Entity]]] constrain(t:assignment(AstNode lt, AstNode rt), CompilUnit facts, Mapper mapper) 
	= { subtype(lookup_(facts, mapper, rmv(rt)), lookup_(facts, mapper, rmv(lt))) }
	;
public set[Constraint[BLogger[Entity]]] constrain(t:castExpression(_, AstNode e), CompilUnit facts, Mapper mapper) 
	= { (isDownCast(facts, mapper, t)) ? subtype(lookup_(facts, mapper, t), lookup_(facts, mapper, rmv(e))) 
									   : subtype(lookup_(facts, mapper, rmv(e)), lookup_(facts, mapper, t)) }
	;
public set[Constraint[BLogger[Entity]]] constrain(t:classInstanceCreation(none(),_, [], [],_), CompilUnit facts, Mapper mapper) 
	= {};
public set[Constraint[BLogger[Entity]]] constrain(t:classInstanceCreation(none(),_, [], list[AstNode] args,_), CompilUnit facts, Mapper mapper) 
	= { subtype(lookup_(facts, mapper, rmv(args[i])), bind(lookup_(facts, mapper, t), param_(i))) | int i <- [0..size(args) - 1], args[i] != nullLiteral() }
	;
public set[Constraint[BLogger[Entity]]] constrain(t:classInstanceCreation(some(AstNode e),_, [], list[AstNode] args, none()), CompilUnit facts, Mapper mapper) {
	if(isEmpty(args)) return {};
	return  { subtype(lookup_(facts, mapper, rmv(args[i])), bind(lookup_(facts, mapper, t), param_(i))) | int i <- [0..size(args) - 1], args[i] != nullLiteral() } 
		  + { subtype(lookup_(facts, mapper, rmv(e)), bind(lookup_(facts, mapper, t), decl_)) };
}	
public set[Constraint[BLogger[Entity]]] constrain(t:classInstanceCreation(_,_, [], list[AstNode] args, some(AstNode anonym)), CompilUnit facts, Mapper mapper) 
	= {};
public set[Constraint[BLogger[Entity]]] constrain(t:conditionalExpression(AstNode _, AstNode thenBranch, AstNode elseBranch), CompilUnit facts, Mapper mapper) 
	=   { subtype(lookup_(facts, mapper, t), lookup_(facts, mapper, rmv(thenBranch))) }
	  + { subtype(lookup_(facts, mapper, t), lookup_(facts, mapper, rmv(elseBranch))) }
	;
public set[Constraint[BLogger[Entity]]] constrain(t:constructorInvocation(_, list[AstNode] args), CompilUnit facts, Mapper mapper) {
	if(isEmpty(args)) return {};
	return { subtype(lookup_(facts, mapper, rmv(args[i])), bind(lookup_(facts, mapper, t), param_(i))) | int i <- [0..size(args) - 1], args[i] != nullLiteral() };
}
public set[Constraint[BLogger[Entity]]] constrain(t:fieldAccess(AstNode e,_), CompilUnit facts, Mapper mapper) 
	= { eq(lookup_(facts, mapper, rmv(e)), bind(lookup_(facts, mapper, t), decl_)) }
	;
public set[Constraint[BLogger[Entity]]] constrain(t:methodInvocation(none(),_,_, list[AstNode] args), CompilUnit facts, Mapper mapper) {
	if(isEmpty(args)) return {};
	return { subtype(lookup_(facts, mapper, rmv(args[i])), bind(lookup_(facts, mapper, t), param_(i))) | int i <- [0..size(args) - 1], args[i] != nullLiteral() };
}
public set[Constraint[BLogger[Entity]]] constrain(t:methodInvocation(some(AstNode e),_,_, list[AstNode] args), CompilUnit facts, Mapper mapper) { 
	set[Constraint[BLogger[Entity]]] cons = { subtype(lookup_(facts, mapper, rmv(e)), bind(lookup_(facts, mapper, t), decl_)) };
	if(isEmpty(args)) return cons; 
	set[Constraint[BLogger[Entity]]] cons_ = { subtype(lookup_(facts, mapper, rmv(args[i])), bind(lookup_(facts, mapper, t), param_(i))) | int i <- [0..size(args) - 1], args[i] != nullLiteral() };
	return cons + cons_;
}
public set[Constraint[BLogger[Entity]]] constrain(t:qualifiedName(_,_), CompilUnit facts, Mapper mapper) 
	= {};
public set[Constraint[BLogger[Entity]]] constrain(t:superConstructorInvocation(some(AstNode e), _, list[AstNode] args), CompilUnit facts, Mapper mapper) {
	set[Constraint[BLogger[Entity]]] cons = { subtype(lookup_(facts, mapper, rmv(e)), bind(lookup_(facts, mapper, t), decl_)) };
	if(isEmpty(args)) return cons;
	set[Constraint[BLogger[Entity]]] cons_ = { subtype(lookup_(facts, mapper, rmv(args[i])), bind(lookup(facts, mapper, t), param_(i))) | int i <- [0..size(args) - 1], args[i] != nullLiteral() };
	return cons + cons_;
}
public set[Constraint[BLogger[Entity]]] constrain(t:superFieldAccess(_,_), CompilUnit facts, Mapper mapper) 
	= {};
public set[Constraint[BLogger[Entity]]] constrain(t:superMethodInvocation(_,_,_, list[AstNode] args), CompilUnit facts, Mapper mapper) {
	if(isEmpty(args)) return {};
	return { subtype(lookup_(facts, mapper, rmv(args[i])), bind(lookup_(facts, mapper, t), param_(i))) | int i <- [0..size(args) - 1], args[i] != nullLiteral() };
}
public set[Constraint[BLogger[Entity]]] constrain(t:singleVariableDeclaration(str name,_,_, some(nullLiteral()),_), CompilUnit facts, Mapper mapper) 
	= {};
public set[Constraint[BLogger[Entity]]] constrain(t:singleVariableDeclaration(str name,_,_, some(AstNode initializer),_), CompilUnit facts, Mapper mapper) 
	= { subtype(lookup_(facts, mapper, rmv(initializer)), lookup_(facts, mapper, setAnnotations(simpleName(name), getAnnotations(t)))) }
	;
public set[Constraint[BLogger[Entity]]] constrain(t:variableDeclarationFragment(str name, some(nullLiteral())), CompilUnit facts, Mapper mapper) 
	= {};
public set[Constraint[BLogger[Entity]]] constrain(t:variableDeclarationFragment(str name, some(AstNode initializer)), CompilUnit facts, Mapper mapper) 
	= { subtype(lookup_(facts, mapper, rmv(initializer)), lookup_(facts, mapper, setAnnotations(simpleName(name), getAnnotations(t)))) }
	;
public default set[Constraint[BLogger[Entity]]] constrain(AstNode t, CompilUnit facts, Mapper mapper) = {};

// ======================================================================================================================================

public Constraint[BLogger[Entity]] evalC(CompilUnit facts, Mapper mapper, Constraint c) {	
	BLogger[Entity] (Entity) eval__ = evalLogger(mapper) o eval_;
	BLogger[Entity] lh_ = bind(c.lh, eval__);
	BLogger[Entity] rh_ = bind(c.rh, eval__);
	switch(c) {
		case eq(_,_) : return eq(lh_, rh_);
		case subtype(_,_) : return subtype(lh_, rh_);
	}	
}

public Constraint[BLogger[Entity]] supertypesC(CompilUnit facts, Mapper mapper, Constraint c) {
	BLogger[bool] (CompilUnit, Entity, Entity) supertypes_ = superTypesLogger(mapper) o superTypesGens(mapper) o superTypes;
	Entity rh = mkSubstsExplicit(mapper, eval(c.rh)).genval;
	BLogger[Entity] lh_ = bind(c.lh, BLogger[Entity] (Entity v) { 
									return bind(supertypes_(facts, mkSubstsExplicit(mapper, v).genval, rh), BLogger[Entity] (bool b) {
													assert(b);
													return returnBL(rh); }); });
	BLogger[Entity] rh_ = bind(c.rh, BLogger[Entity] (Entity _) { return returnBL(rh); });
	switch(c) {
		case eq(_,_) : return eq(lh_, rh_);
		case subtype(_,_) : return eq(lh_, rh_);
	}	
}

public Constraint[BLogger[Entity]] boundUBLB(CompilUnit facts, Mapper mapper, Constraint c) {
	BLogger[Entity] (Entity) eval__ = evalLogger(mapper) o eval_;
	BLogger[Entity] lh_ = bind(c.lh, BLogger[Entity] (Entity lh) { 
								return bind(eval__(lh), BLogger[Entity] (Entity _) { 
									return boundUB(facts, mapper, eval(mkSubstsExplicit(mapper, lh).genval)); }); });
	BLogger[Entity] rh_ = bind(c.rh, BLogger[Entity] (Entity rh) {
								return bind(eval__(rh), BLogger[Entity] (Entity _) { 
									return boundLB(facts, mapper, eval(mkSubstsExplicit(mapper, rh).genval)); }); });
	switch(c) {
		case eq(_,_) : return subtype(lh_, rh_);
		case subtype(_,_) : return subtype(lh_, rh_);
	}	
}

public Constraint[BLogger[Entity]] bound_ublb(CompilUnit facts, Mapper mapper, Constraint c) {
	BLogger[Entity] (Entity) eval__ = evalLogger(mapper) o eval_;
	BLogger[Entity] lh_ = bind(c.lh, BLogger[Entity] (Entity lh) {
								return bind(eval__(lh), BLogger[Entity] (Entity _) { 
									return bound_ub0(facts, mapper, eval(mkSubstsExplicit(mapper, lh).genval)); }); });
	BLogger[Entity] rh_ = bind(c.rh, BLogger[Entity] (Entity rh) {
								return bind(eval__(rh), BLogger[Entity] (Entity _) { 
									return bound_lb(facts, mapper, eval(mkSubstsExplicit(mapper, rh).genval)); }); });
	switch(c) {
		case eq(_,_) : return subtype(lh_, rh_);
		case subtype(_,_) : return subtype(lh_, rh_);
	}		
}

public Constraint[BLogger[Entity]] boundUBUB(CompilUnit facts, Mapper mapper, Constraint c) {
	BLogger[Entity] (Entity) eval__ = evalLogger(mapper) o eval_;
	BLogger[Entity] lh_ = bind(c.lh, BLogger[Entity] (Entity lh) { 
								return bind(eval__(lh), BLogger[Entity] (Entity _) { 
									return boundUB(facts, mapper, eval(mkSubstsExplicit(mapper, lh).genval)); }); });
	BLogger[Entity] rh_ = bind(c.rh, BLogger[Entity] (Entity rh) {
								return bind(eval__(rh), BLogger[Entity] (Entity _) { 
									return boundUB(facts, mapper, eval(mkSubstsExplicit(mapper, rh).genval)); }); });
	switch(c) {
		case eq(_,_) : return subtype(lh_, rh_);
		case subtype(_,_) : return subtype(lh_, rh_);
	}	
}

public Constraint[BLogger[Entity]] bound_ubub(CompilUnit facts, Mapper mapper, Constraint c) {
	BLogger[Entity] (Entity) eval__ = evalLogger(mapper) o eval_;
	BLogger[Entity] lh_ = bind(c.lh, BLogger[Entity] (Entity lh) {
								return bind(eval__(lh), BLogger[Entity] (Entity _) { 
									return bound_ub0(facts, mapper, eval(mkSubstsExplicit(mapper, lh).genval)); }); }); 
	BLogger[Entity] rh_ = bind(c.rh, BLogger[Entity] (Entity rh) {
								return bind(eval__(rh), BLogger[Entity] (Entity _) { 
									return bound_ub(facts, mapper, eval(mkSubstsExplicit(mapper, rh).genval)); }); });
	switch(c) {
		case eq(_,_) : return subtype(lh_, rh_);
		case subtype(_,_) : return subtype(lh_, rh_);
	}		
}

public Constraint[BLogger[Entity]] boundLBLB(CompilUnit facts, Mapper mapper, Constraint c) {
	BLogger[Entity] (Entity) eval__ = evalLogger(mapper) o eval_;
	BLogger[Entity] lh_ = bind(c.lh, BLogger[Entity] (Entity lh) { 
								return bind(eval__(lh), BLogger[Entity] (Entity _) { 
									return boundLB(facts, mapper, eval(mkSubstsExplicit(mapper, lh).genval)); }); });
	BLogger[Entity] rh_ = bind(c.rh, BLogger[Entity] (Entity rh) {
								return bind(eval__(rh), BLogger[Entity] (Entity _) { 
									return boundLB(facts, mapper, eval(mkSubstsExplicit(mapper, rh).genval)); }); });
	switch(c) {
		case eq(_,_) : return subtype(rh_, lh_);
		case subtype(_,_) : return subtype(rh_, lh_);
	}	
}

public Constraint[BLogger[Entity]] bound_lblb(CompilUnit facts, Mapper mapper, Constraint c) {
	BLogger[Entity] (Entity) eval__ = evalLogger(mapper) o eval_;
	BLogger[Entity] lh_ = bind(c.lh, BLogger[Entity] (Entity lh) {
								return bind(eval__(lh), BLogger[Entity] (Entity v) { 
									return bound_lb(facts, mapper, eval(mkSubstsExplicit(mapper, lh).genval)); }); }); 
	BLogger[Entity] rh_ = bind(c.rh, BLogger[Entity] (Entity rh) {
								return bind(eval__(rh), BLogger[Entity] (Entity v) { 
									return bound_lb(facts, mapper, eval(mkSubstsExplicit(mapper, rh).genval)); }); });
	switch(c) {
		case eq(_,_) : return subtype(rh_, lh_);
		case subtype(_,_) : return subtype(rh_, lh_);
	}		
}

public set[Constraint[BLogger[Entity]]] closure(CompilUnit facts, Mapper mapper, c:Constraint::subtype(_,_)) { // tracer(true, "closure of <prettyprint(c)> -- <prettyprint(evalb(c.lh))> -- <prettyprint(evalb(c.rh))>");
	Constraint[BLogger[Entity]] c_ = boundUBLB(facts, mapper, c);
	Constraint[BLogger[Entity]] c__ = bound_ublb(facts, mapper, c);
	set[Constraint[BLogger[Entity]]] cons = {};	
	cons = cons + handleTypeArgumentsOfRawTypes(facts, mapper, c_, c__);
	return cons + equalizeParamTypes(facts, mapper, c__);
}
public set[Constraint[BLogger[Entity]]] closure(CompilUnit facts, Mapper mapper, c:Constraint::eq(_,_)) = {};

public set[Constraint[BLogger[Entity]]] handleTypeArgumentsOfRawTypes(CompilUnit facts, Mapper mapper, Constraint[BLogger[Entity]] c, Constraint[BLogger[Entity]] c_) {
	Entity lh  = eval(c.lh);
	Entity rh  = eval(c.rh);
	Entity lh_ = eval(c_.lh);
	Entity rh_ = eval(c_.rh);
	if( ( isTypeArgument(lh) && getInit(lh) == zero() ) || ( isTypeArgument(rh) && getInit(rh) == zero() ) ) {

		if( ( isTypeArgument(lh) && getInit(lh) == zero() ) && rh_ != zero() ) {
			PEntity prh = mkSubstsExplicit(mapper, rh_);
			Bindings logbs = parameterize(mapper, bindings([ pzero() | Entity _ <- prh.bindings.params ], prh.bindings.params), lh);
			return equalizeParamTypes(facts, mapper, subtype(bind(c_.lh, BLogger[Entity] (Entity _) {
																	return bind(log(logbs), BLogger[Entity] (value _) {
																			return returnBL(rh_); }); }), 
															 c_.rh));
		}
		if( lh_ != zero() && ( isTypeArgument(rh) && getInit(rh) == zero() ) ) {
			println("handle raw types: <prettyprint(c)> --- <prettyprint(c_)>");
			PEntity plh = mkSubstsExplicit(mapper, lh_);
			Bindings logbs = parameterize(mapper, bindings([ pzero() | Entity _ <- plh.bindings.params ], plh.bindings.params), rh);
			println("<prettyprint(logbs)>");
			return equalizeParamTypes(facts, mapper, subtype(c_.lh, 
															 bind(c_.rh, BLogger[Entity] (Entity _) {
																	return bind(log(logbs), BLogger[Entity] (value _) {
																			return returnBL(lh_); }); })));
		}
	}
	return {};
}

public set[Constraint[BLogger[Entity]]] handleNonGenericTypes(CompilUnit facts, Mapper mapper, Constraint[BLogger[Entity]] c, Constraint[BLogger[Entity]] c_) {
	Entity lh = eval(c.lh);
	Entity rh = eval(c.rh);
	Entity lh_ = eval(c_.lh);
	Entity rh_ = eval(c_.rh);
	
	PEntity ptlh = mkSubstsExplicit(mapper, eval(mkSubstsExplicit(mapper, lh).genval));
	PEntity ptrh = mkSubstsExplicit(mapper, eval(mkSubstsExplicit(mapper, rh).genval));
	PEntity ptlh_ = mkSubstsExplicit(mapper, lh_);
	PEntity ptrh_ = mkSubstsExplicit(mapper, rh_);
	
	if( isEmpty(getTypeParamsOrArgs(ptlh.genval)) && !isTypeParameter(ptlh.genval) && !isEmpty(getTypeParamsOrArgs(ptrh_.genval))) {
		return equalizeParamTypes(facts, mapper, bind(log(parameterize(mapper, bindings([ pzero() | Entity _ <- ptrh_.bindings.params ], ptrh_.bindings.params), lh)), BLogger[Entity] (value _) {
													return returnBL(rh_); }),
											c_.rh);	
	} 
	if(isEmpty(getTypeParamsOrArgs(ptrh.genval)) && !isTypeParameter(ptrh.genval) && !isEmpty(getTypeParamsOrArgs(ptlh_.genval))) {
		return equalizeParamTypes(facts, mapper, c_.lh, 
											bind(log(parameterize(mapper, bindings([ pzero() | Entity _ <- ptlh_.bindings.params ], ptlh_.bindings.params), rh)), BLogger[Entity] (value _) {
													return returnBL(c_.lh); }));	
	} 
	return {};
}

public set[Constraint[BLogger[Entity]]] equalizeParamTypes(CompilUnit facts, Mapper mapper, c:Constraint::subtype(_,_)) {
	if(eval(c.lh) != zero() && eval(c.rh) != zero()) {  // tracer(true, "equalize parameterized types: <prettyprint(c)> ; <prettyprint(evalb(c.lh))> --- <prettyprint(evalb(c.rh))>");
		Constraint[BLogger[Entity]] c_ = supertypesC(facts, mapper, c);
		assert(eval(c_.lh) == eval(c_.rh));
		PEntity pv = mkSubstsExplicit(mapper, eval(c.rh));
		if(!isEmpty(pv.bindings.params))
			return { *equalizeTBounds(facts, mapper, eq(bind(c_.lh, BLogger[Entity] (Entity v) { return returnBL(pv.bindings.params[i]); }),
												  	  	bind(c_.rh, BLogger[Entity] (Entity v) { return returnBL(pv.bindings.params[i]); }))) 
																	| int i <- [0..size(pv.bindings.params) - 1] };		
	}
	return {};
}

public set[Constraint[BLogger[Entity]]] equalizeTBounds(CompilUnit facts, Mapper mapper, c:Constraint::eq(_,_)) 
	= equalizeTBounds_UB(facts, mapper, c) 
	+ equalizeTBounds_LB(facts, mapper, c)
	+ equalizeTBounds_ub(facts, mapper, c)  
	+ equalizeTBounds_lb(facts, mapper, c);

public set[Constraint[BLogger[Entity]]] equalizeTBounds_UB(CompilUnit facts, Mapper mapper, c:Constraint::eq(_,_)) {
	set[Constraint[BLogger[Entity]]] cons = {};
	Constraint[BLogger[Entity]] c_UBUB = boundUBUB(facts, mapper, c);
	if(isTypeArgument(eval(c_UBUB.lh)) || isTypeArgument(eval(c_UBUB.rh)))
		cons += c_UBUB;
	if(isTypeArgument(eval(c_UBUB.lh)))
		cons += subtype(bound_ub(facts, mapper, eval(c_UBUB.lh)), (parameterizer1(mapper) o substsLogger(mapper) o boundT)(facts, getTypeParameter(eval(c_UBUB.lh))));
	if(isTypeArgument(eval(c_UBUB.rh)))
		cons += subtype(bound_ub(facts, mapper, eval(c_UBUB.rh)), (parameterizer1(mapper) o substsLogger(mapper) o boundT)(facts, getTypeParameter(eval(c_UBUB.rh))));
	cons = cons + handleTypeArgumentsOfRawTypes(facts, mapper, boundUBUB(facts, mapper, c), bound_ubub(facts, mapper, c));
	return cons;
}

public set[Constraint[BLogger[Entity]]] equalizeTBounds_LB(CompilUnit facts, Mapper mapper, c:Constraint::eq(_,_)) {
	set[Constraint[BLogger[Entity]]] cons = {};
	Constraint[BLogger[Entity]] c_LBLB = boundLBLB(facts, mapper, c);
	if(isTypeArgument(eval(c_LBLB.lh)) || isTypeArgument(eval(c_LBLB.rh)))
		cons += c_LBLB;
	cons = cons + handleTypeArgumentsOfRawTypes(facts, mapper, boundLBLB(facts, mapper, c), bound_lblb(facts, mapper, c));
	return cons;
}

public set[Constraint[BLogger[Entity]]] equalizeTBounds_ub(CompilUnit facts, Mapper mapper, c:Constraint::eq(_,_)) {
	return equalizeParamTypes(facts, mapper, bound_ubub(facts, mapper, c));
}

public set[Constraint[BLogger[Entity]]] equalizeTBounds_lb(CompilUnit facts, Mapper mapper, c:Constraint::eq(_,_)) {
	return equalizeParamTypes(facts, mapper, bound_lblb(facts, mapper, c));
}

// ==================================================================================================

public str prettyprint(Constraint::eq(BLogger[Entity] lh, BLogger[Entity] rh)) = "<prettyprint(eval(lh))> == <prettyprint(eval(rh))>"; 
public str prettyprint(Constraint::subtype(BLogger[Entity] lh, BLogger[Entity] rh)) = "<prettyprint(eval(lh))> \<: <prettyprint(eval(rh))>"; 

public str prettyprint(Constraint::eq(&M lh, &M rh)) = "<prettyprint(lh)> == <prettyprint(rh)>"; 
public str prettyprint(Constraint::subtype(&M lh, &M rh)) = "<prettyprint(lh)> \<: <prettyprint(rh)>"; 
