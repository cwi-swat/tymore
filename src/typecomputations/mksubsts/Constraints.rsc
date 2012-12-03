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
					  		 | subtype(&M lh, &M rh);

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

public set[Constraint[BLogger[Entity]]] closure(CompilUnit facts, Mapper mapper, c:Constraint::subtype(BLogger[Entity] val1, BLogger[Entity] val2)) {
	BLogger[Entity] (Entity) eval__ = evalLogger(mapper) o eval_;
	BLogger[bool] (CompilUnit, Entity, Entity) supertypes_ = superTypesLogger(mapper) o superTypesGens(mapper) o superTypes;
	
	Entity v1 = eval(val1);
	Entity v2 = eval(val2);
	
	// tracer(true, "Subtyping in: <prettyprint(v1)> -- <prettyprint(v2)> -;- <prettyprint(evalb(val1))> -- <prettyprint(evalb(val2))>");
	
	// Bound that catches type argument constraints
	BLogger[Entity] val1_ = bind(bind(val1, eval__), BLogger[Entity] (Entity v) { 
									Entity gen = eval(mkSubstsExplicit(mapper, v1).genval);
									return bind(bound(facts, mapper, gen), BLogger[Entity] (Entity b) {
													return returnBL(b); }); });
	BLogger[Entity] val2_ = bind(bind(val2, eval__), BLogger[Entity] (Entity v) { 
									Entity gen = eval(mkSubstsExplicit(mapper, v2).genval);
									return bind(bound(facts, mapper, gen), BLogger[Entity] (Entity b) {
													return returnBL(b); }); });
		
	Entity v1_ = eval(val1_);
	Entity v2_ = eval(val2_);
	
	// tracer(true, "Subtyping middle: <prettyprint(v1_)> -- <prettyprint(v2_)> -;- <prettyprint(evalb(val1_))> -- <prettyprint(evalb(val2_))>");
	
	// Bound that catches the generic types, the subtype relation can originate due to wild cards (Java covariance)
	BLogger[Entity] val1__ = bind(bind(val1, eval__), BLogger[Entity] (Entity v) { 
									Entity gen = eval(mkSubstsExplicit(mapper, v1).genval);
									if(isTypeParameter(gen))
										return bind(bound_(facts, mapper, gen), BLogger[Entity] (Entity b) {
														return returnBL(b); });
									return returnBL(eval(boundT(facts, eval(boundWildcard(facts, mapper, v))))); }); // does not seem to be necessary
	BLogger[Entity] val2__ = bind(bind(val2, eval__), BLogger[Entity] (Entity v) { 
									Entity gen = eval(mkSubstsExplicit(mapper, v2).genval);
									if(isTypeParameter(gen))
										return bind(bound_(facts, mapper, gen), BLogger[Entity] (Entity b) {
														return returnBL(b); });
									return returnBL(eval(boundT(facts, eval(boundWildcard(facts, mapper, v))))); }); // does not seem to be necessary
		
	Entity v1__ = eval(val1__);
	Entity v2__ = eval(val2__);
	
	// tracer(true, "Subtyping out: <prettyprint(v1__)> -- <prettyprint(v2__)> -;- <prettyprint(evalb(val1__))> -- <prettyprint(evalb(val2__))>");
	
	// Handles raw types								
	if((isTypeArgument(v1_) && (getInit(v1_) == zero())) 
		|| (isTypeArgument(v2_) && (getInit(v2_) == zero()))) {
		
		if( (isTypeArgument(v1_) && getInit(v1_) == zero()) 
			&& !(isTypeArgument(v2_) && getInit(v2_) == zero()) ) {
			PEntity pval2 = mkSubstsExplicit(mapper, v2__);
			Bindings logbs = parameterize(bindings([ pzero() | Entity _ <- pval2.bindings.params ], pval2.bindings.params), v1_);
			return equalizeTypes(facts, mapper, bind(val1__, BLogger[Entity] (Entity _) {
														return bind(log(logbs), BLogger[Entity] (value _) {
																		return returnBL(v2__); }); }), 
												val2__);
		}
		if( (isTypeArgument(v2_) && getInit(v2_) == zero()) 
			&& !(isTypeArgument(v1_) && getInit(v1_) == zero()) ) {
			PEntity pval1 = mkSubstsExplicit(mapper, v1__);
			println("v1 : <prettyprint(v1__)>");
			Bindings logbs = parameterize(bindings([ pzero() | Entity _ <- pval1.bindings.params ], pval1.bindings.params), v2_);
			return equalizeTypes(facts, mapper, val1__, 
												bind(val2__, BLogger[Entity] (Entity _) {
														return bind(log(logbs), BLogger[Entity] (value _) {
																		return returnBL(v1__); }); }));
		}
	}
	
	v1 = eval(val1);
	v2 = eval(val2);
	
	Entity tv1 = eval(mkSubstsExplicit(mapper, v1).genval);
	Entity tv2 = eval(mkSubstsExplicit(mapper, v2).genval);
	
	PEntity ptv1 = mkSubstsExplicit(mapper, tv1);
	PEntity ptv2 = mkSubstsExplicit(mapper, tv2);
	
	PEntity ptv1__ = mkSubstsExplicit(mapper, v1__);
	PEntity ptv2__ = mkSubstsExplicit(mapper, v2__);
	
	if(isEmpty(getTypeParamsOrArgs(ptv1.genval)) && !isTypeParameter(ptv1.genval) && !isEmpty(getTypeParamsOrArgs(ptv2__.genval))) {
		return equalizeTypes(facts, mapper, bind(log(parameterize(bindings([ pzero() | Entity _ <- ptv2__.bindings.params ], ptv2__.bindings.params), v1)), BLogger[Entity] (value _) {
													return returnBL(v2__); }),
											val2__);	
	} 
	if(isEmpty(getTypeParamsOrArgs(ptv2.genval)) && !isTypeParameter(ptv2.genval) && !isEmpty(getTypeParamsOrArgs(ptv1__.genval))) {
		return equalizeTypes(facts, mapper, val1__, 
											bind(log(parameterize(bindings([ pzero() | Entity _ <- ptv1__.bindings.params ], ptv1__.bindings.params), v2)), BLogger[Entity] (value _) {
													return returnBL(v1__); }));	
	} 
					
	return equalizeTypes(facts, mapper, val1__, val2__);
}

public set[Constraint[BLogger[Entity]]] closure(CompilUnit facts, Mapper mapper, c:Constraint::eq(BLogger[Entity] val1, BLogger[Entity] val2)) {
	BLogger[Entity] (Entity) eval__ = evalLogger(mapper) o eval_;
	
	Entity v1 = eval(val1);
	Entity v2 = eval(val2);
	
	// Bound that catches type argument constraints
	BLogger[Entity] val1_ = bind(bind(val1, eval__), BLogger[Entity] (Entity v) { 
									Entity gen = eval(mkSubstsExplicit(mapper, v1).genval);
									return bind(bound(facts, mapper, gen), BLogger[Entity] (Entity b) {
													return returnBL(b); }); });
	BLogger[Entity] val2_ = bind(bind(val2, eval__), BLogger[Entity] (Entity v) { 
									Entity gen = eval(mkSubstsExplicit(mapper, v2).genval);
									return bind(bound(facts, mapper, gen), BLogger[Entity] (Entity b) {
													return returnBL(b); }); });
		
	Entity v1_ = eval(val1_);
	Entity v2_ = eval(val2_);
	
	// Bound that catches the generic types, the subtype relation can originate due to wild cards (Java covariance)
	BLogger[Entity] val1__ = bind(bind(val1, eval__), BLogger[Entity] (Entity v) { 
									Entity gen = eval(mkSubstsExplicit(mapper, v1).genval);
									if(isTypeParameter(gen))
										return bind(bound_(facts, mapper, gen), BLogger[Entity] (Entity b) {
														return returnBL(b); });
									return returnBL(eval(boundT(facts, eval(boundWildcard(facts, mapper, v))))); }); // does not seem to be necessary
	BLogger[Entity] val2__ = bind(bind(val2, eval__), BLogger[Entity] (Entity v) { 
									Entity gen = eval(mkSubstsExplicit(mapper, v2).genval);
									if(isTypeParameter(gen))
										return bind(bound_(facts, mapper, gen), BLogger[Entity] (Entity b) {
														return returnBL(b); });
									return returnBL(eval(boundT(facts, eval(boundWildcard(facts, mapper, v))))); }); // does not seem to be necessary
	
	Entity v1__ = eval(val1__);
	Entity v2__ = eval(val2__);
	
	// Handles raw types								
	if((isTypeArgument(v1_) && (getInit(v1_) == zero())) 
		|| (isTypeArgument(v2_) && (getInit(v2_) == zero()))) {
		
		if( (isTypeArgument(v1_) && getInit(v1_) == zero()) 
			&& !(isTypeArgument(v2_) && getInit(v2_) == zero()) ) {
			PEntity pval2 = mkSubstsExplicit(mapper, v2__);
			Bindings logbs = parameterize(bindings([ pzero() | Entity _ <- pval2.bindings.params ], pval2.bindings.params), v1_);
			return equalizeTypes(facts, mapper, bind(val1__, BLogger[Entity] (Entity _) {
														return bind(log(logbs), BLogger[Entity] (value _) {
																		return returnBL(v2__); }); }), 
												val2__);
		}
		if( (isTypeArgument(v2_) && getInit(v2_) == zero()) 
			&& !(isTypeArgument(v1_) && getInit(v1_) == zero()) ) {
			PEntity pval1 = mkSubstsExplicit(mapper, v1__);
			Bindings logbs = parameterize(bindings([ pzero() | Entity _ <- pval1.bindings.params ], pval1.bindings.params), v2_);
			return equalizeTypes(facts, mapper, val1__, 
												bind(val2__, BLogger[Entity] (Entity _) {
														return bind(log(logbs), BLogger[Entity] (value _) {
																		return returnBL(v1__); }); }));
		}
	}
				
	return equalizeTypes(facts, mapper, val1__, val2__);
}

public set[Constraint[BLogger[Entity]]] equalizeTypes(CompilUnit facts, Mapper mapper, BLogger[Entity] val1, BLogger[Entity] val2) {
	
	BLogger[bool] (CompilUnit, Entity, Entity) supertypes_ = superTypesLogger(mapper) o superTypesGens(mapper) o superTypes;
	
	set[Constraint[BLogger[Entity]]] cons = {};
	
	Entity v1 = eval(val1);
	Entity v2 = eval(val2);
	
	// tracer(true, "Equalize in: <prettyprint(v1)> -- <prettyprint(v2)> -;- <prettyprint(evalb(val1))> -- <prettyprint(evalb(val2))>");
		
	// Bound that catches type argument constraints
	BLogger[Entity] val1_ = bind(val1, BLogger[Entity] (Entity v) { 
									return bound(facts, mapper, v); });
	BLogger[Entity] val2_ = bind(val2, BLogger[Entity] (Entity v) { 
									return bound(facts, mapper, v); });
		
	Entity v1_ = eval(val1_);
	Entity v2_ = eval(val2_);
	
	// tracer(true, "Equalize middle: <prettyprint(v1_)> -- <prettyprint(v2_)> -;- <prettyprint(evalb(val1_))> -- <prettyprint(evalb(val2_))>");
	
	if(isTypeArgument(v1_) || isTypeArgument(v2_)) 
		cons += eq(val1_, val2_);
	
	// Bound that catches the generic types, the subtype relation can originate due to wild cards (Java covariance)
	BLogger[Entity] val1__ = bind(val1, BLogger[Entity] (Entity v) { 
									return bound_(facts, mapper, v); });
	BLogger[Entity] val2__ = bind(val2, BLogger[Entity] (Entity v) { 
									return bound_(facts, mapper, v); });
	
	Entity v1__ = eval(val1__);
	Entity v2__ = eval(val2__);
	
	// Handles raw types								
	if((isTypeArgument(v1_) && getInit(v1_) == zero()) 
		|| (isTypeArgument(v2_) && (getInit(v2_) == zero()))) {
		if( (isTypeArgument(v1_) && getInit(v1_) == zero()) 
			&& !(isTypeArgument(v2_) && getInit(v2_) == zero()) ) {
			PEntity pval2 = mkSubstsExplicit(mapper, v2__);
			Bindings logbs = parameterize(bindings([ pzero() | Entity _ <- pval2.bindings.params ], pval2.bindings.params), v1_);
			return cons + equalizeTypes(facts, mapper, bind(val1__, BLogger[Entity] (Entity _) {
																		return bind(log(logbs), BLogger[Entity] (value _) {
																			return returnBL(v2__); }); }), 
													   val2__);
		}
		if( (isTypeArgument(v2_) && getInit(v2_) == zero()) 
			&& !(isTypeArgument(v1_) && getInit(v1_) == zero()) ) {
			PEntity pval1 = mkSubstsExplicit(mapper, v1__);
			Bindings logbs = parameterize(bindings([ pzero() | Entity _ <- pval1.bindings.params ], pval1.bindings.params), v2_);
			return cons + equalizeTypes(facts, mapper, val1__, 
													   bind(val2__, BLogger[Entity] (Entity _) {
															return bind(log(logbs), BLogger[Entity] (value _) {
																			return returnBL(v1__); }); }));
		}
	}
	
	bool b1 = false;
	bool b2 = false;
	
	BLogger[Entity] val1___ = bind(val1__, BLogger[Entity] (Entity v) { 
									return bind(supertypes_(facts, v, v2__), BLogger[Entity] (bool b) {
													b1 = b;
													if(b) return returnBL(v2__);
													return val1__; }); });
	BLogger[Entity] val2___ = bind(val2__, BLogger[Entity] (Entity v) { 
									return bind(supertypes_(facts, v, v1__), BLogger[Entity] (bool b) {
													b2 = b;
													if(b) return returnBL(v1__);
													return val2__; }); });
	
	Entity v1___ = eval(val1___);
	Entity v2___ = eval(val2___);
	
	// tracer(true, "equalize out: <prettyprint(v1___)> -- <prettyprint(v2___)> -;- <prettyprint(evalb(val1___))> -- <prettyprint(evalb(val2___))>");
		
	assert(mkSubstsExplicit(mapper, v1___).genval == mkSubstsExplicit(mapper, v2___).genval);
	
	PEntity pval = mkSubstsExplicit(mapper, (b1) ? v1___ : v2___);
	if(!isEmpty(pval.bindings.params))
		cons = cons + { *equalizeTypes(facts, mapper, bind(val1___, BLogger[Entity] (Entity v) {
															return returnBL(pval.bindings.params[i]); }),
												  	  bind(val2___, BLogger[Entity] (Entity v) {
															return returnBL(pval.bindings.params[i]); })) 
																| int i <- [0..size(pval.bindings.params) - 1] };
	return cons;
}

// ==================================================================================================

public str prettyprint(Constraint::eq(BLogger[Entity] lh, BLogger[Entity] rh)) = "<prettyprint(eval(lh))> == <prettyprint(eval(rh))>"; 
public str prettyprint(Constraint::subtype(BLogger[Entity] lh, BLogger[Entity] rh)) = "<prettyprint(eval(lh))> \<: <prettyprint(eval(rh))>"; 

public str prettyprint(Constraint::eq(&M lh, &M rh)) = "<prettyprint(lh)> == <prettyprint(rh)>"; 
public str prettyprint(Constraint::subtype(&M lh, &M rh)) = "<prettyprint(lh)> \<: <prettyprint(rh)>"; 
