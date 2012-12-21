module typecomputations::mksubsts::TypeComputations

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;
import lang::java::jdt::refactorings::PrettyPrintUtil;
import lang::java::jdt::refactorings::ValuesUtil;

import typecomputations::TypeValues;

import IO;
import List;
import Map;
import Set;


public data BLogger[&T] = blogger( tuple[&T, Bindings] (Bindings) val );

public BLogger[&T] returnBL(&T val) = blogger(tuple[&T, Bindings] (Bindings bs) { return <val, bs>; });
public tuple[&T, Bindings] (Bindings) run(BLogger[&T] mval) = tuple[&T, Bindings] (Bindings bs) { return mval.val(bs); };
public &T eval(BLogger[&T] mval) = mval.val(bindings([],[]))[0];
public Bindings evalb(BLogger[&T] mval) = mval.val(bindings([],[]))[1];
public BLogger[value] log(Bindings bs) = blogger(tuple[value, Bindings] (Bindings prev) { return <"", concat(prev, bs)>; });
public BLogger[Bindings] fetchBL() = blogger(tuple[Bindings, Bindings] (Bindings bs) { return <bs, bs>; });

public BLogger[&T2] bind(BLogger[&T1] mval, BLogger[&T2] (&T1) f) {
	return blogger( tuple[&T2, Bindings] (Bindings prev) {
						if(<&T1 val1, Bindings bs1> := run(mval)(prev))
						   if(<&T2 val2, Bindings bs2> := run(f(val1))(bs1))
						   		return <val2, bs2>;
					}
				  );
}

// ========== >< ========== >< ========== >< ========== >< ==========

public BLogger[Entity] lookup_(CompilUnit facts, Mapper mapper, AstNode t) 
	= bind( lookup_(t), BLogger[Entity] (Entity val) {
							BLogger[Entity] (Entity) eval__ = evalLogger(mapper) o eval_;
							BLogger[bool] (CompilUnit, Entity, Entity) supertypes_ = superTypesLogger(mapper) o superTypes;
							BLogger[Entity] subLookupType 
								= bind(some(AstNode sub) := subterm(t) ? lookup_(facts, mapper, sub) : returnBL(zero()), BLogger[Entity] (Entity v) {
										if(v == zero()) return returnBL(zero());
										return bind(eval__(v), BLogger[Entity] (Entity v_) {
													return bind(bound_ub(facts, mapper, eval(mkSubstsExplicit(mapper, v).genval)), BLogger[Entity] (Entity _) {
																return returnBL(v_); } ); }); }); 
							return bind(bind(lookup_(t), BLogger[Entity] (Entity v) { 
											return bind(bind(subLookupType, BLogger[Entity] (Entity v_) { return returnBL(boundWcardUB(v_)); }), BLogger[Entity] (Entity v_) {
															if(v_ == zero()) return returnBL(v);
															return bind(supertypes_(facts, v_, eval(decl(v))), BLogger[Entity] (bool _) {
																			return returnBL(v); }); }); }),
										 BLogger[Entity] (Entity v) { return parameterize(mapper, v, t); });
						} );

public BLogger[Entity] lookup_(AstNode t) = returnBL(lookup(t));

public BLogger[Entity] eval_(Entity val) = returnBL(eval(val));

public BLogger[Entity] decl_(Entity val) = returnBL(decl(val));

public BLogger[Entity] (Entity) param_(int i) = BLogger[Entity] (Entity val) { return returnBL(param(i)(val)); };

public BLogger[Entity] (Entity) (BLogger[Entity] (Entity)) evalLogger(Mapper mapper) {
	return BLogger[Entity] (Entity) (BLogger[Entity] (Entity) super) {
		return BLogger[Entity] (Entity val) {
			Entity genval = mkSubstsExplicit(mapper, val).genval;
			Bindings logbs = (genval != eval(genval)) ? parameterize(mapper, mkSubstsExplicit(mapper, eval(genval)).bindings, genval)
													  : bindings([],[]); // tracer(logbs != bindings([],[]), "eval log: <prettyprint(val)> - <prettyprint(logbs)>");
			return bind(log(logbs), BLogger[Entity] (value _) { return super(val); });
		};
	};
}

public list[Entity] supertypes(CompilUnit facts, Entity val) { 
	list[Entity] sups = [ sup | Entity sup <- facts["supertypes_func"][val]]; 
	return isEmpty(sups) ? [ object() ] : sups;
}
public list[Entity] typeParamBounds(CompilUnit facts, Entity val) = [ v | <Entity k, Entity v> <- facts["bounds_func"], k == val];

public BLogger[bool] superTypes(CompilUnit facts, Entity rtype, Entity dtype) {
	if(rtype == object()) return returnBL((rtype == dtype) ? true : false);
	if(rtype == dtype) return returnBL(true);
	if(Entity sup <- supertypes(facts, rtype), BLogger[bool] isSup := superTypes(facts, sup, dtype), eval(isSup)) 
	   	return isSup;
	return returnBL(false);
}

public BLogger[bool] (CompilUnit, Entity, Entity) (BLogger[bool] (CompilUnit, Entity, Entity)) superTypesGens(Mapper mapper) {
	return BLogger[bool] (CompilUnit, Entity, Entity) (BLogger[bool] (CompilUnit, Entity, Entity) super) {
		return BLogger[bool] (CompilUnit facts, Entity rtype, Entity dtype) {
			if(isSubtype(mapper, rtype, dtype)) { //tracer(true, "supertypes in presence of raw types: <prettyprint(rtype)> -- <prettyprint(dtype)>");
				return returnBL(true);
			}
			return super(facts, rtype, dtype);
		};
	};
}

public bool isSubtype(Mapper mapper, Entity sub, Entity sup) = (mkSubstsExplicit(mapper, sub).genval == mkSubstsExplicit(mapper, sup).genval);

public BLogger[bool] (CompilUnit, Entity, Entity) (BLogger[bool] (CompilUnit, Entity, Entity)) superTypesLogger(Mapper mapper) {
	list[Entity] sups = [];
	return BLogger[bool] (CompilUnit, Entity, Entity) (BLogger[bool] (CompilUnit, Entity, Entity) super) {
		return BLogger[bool] (CompilUnit facts, Entity rtype, Entity dtype) { 
		    BLogger[bool] prev = super(facts, rtype, dtype);
		    Bindings logbs = bindings([],[]);
		    if(eval(prev)) { 
		    	if(!isEmpty(sups)) {
		    		PEntity psup = mkSubstsExplicit(mapper, head(sups));
		    		PEntity prtype = mkSubstsExplicit(mapper, rtype);
		    		if(Entity supOfGen <- supertypes(facts, prtype.genval), PEntity psupOfGen := mkSubstsExplicit(mapper, supOfGen), psupOfGen.genval == psup.genval)
		    		   		logbs = parameterize(mapper, psupOfGen.bindings, inherits(prtype.genval, supOfGen));
		    	} // tracer(logbs != bindings([],[]), "sup logbs: <prettyprint(logbs)>");
		    	sups = rtype + sups; 
		    }
		    return bind(log(logbs), BLogger[bool] (value _) { 
		    				return bind(prev, BLogger[bool] (bool b) { 
		    								return returnBL(b); }); });
		};
	};
}

@doc{Extended bound semantics against 'type environment' + 'substitutions'}
public BLogger[Entity] bound_ub(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str _) ])) 
	= bind(boundTSubsts_ub(facts, mapper, tp), BLogger[Entity] (Entity v) { 
			if(v == zero()) return (parameterizer1(mapper) o substsLogger(mapper) o boundT)(facts, tp);
			return bound_ub(facts, mapper, v); });
public BLogger[Entity] bound_ub(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _, _, init) ])) // Ta -> Ta_ub
	= bind((parameterizer2(boundTa_ub))(facts, mapper, entity(ta.id /*+ upper()*/)), BLogger[Entity] (Entity v) {
			return bound_ub(facts, mapper, v); });
public BLogger[Entity] bound_ub(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _, _, _), upper() ])) 
	= bind((parameterizer2(boundTa_ub))(facts, mapper, ta), BLogger[Entity] (Entity v) {
			return bound_ub(facts, mapper, v); });
public BLogger[Entity] bound_ub(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _, _, _), lower() ])) 
	= bind((parameterizer2(boundTa_ub))(facts, mapper, ta), BLogger[Entity] (Entity v) {
			return bound_ub(facts, mapper, v); });
public default BLogger[Entity] bound_ub(CompilUnit facts, Mapper mapper, Entity val) = returnBL(val);

public BLogger[Entity] bound_ub0(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str _) ])) 
	= bind(boundTSubsts_ub(facts, mapper, tp), BLogger[Entity] (Entity v) {
			if(v == zero()) return (parameterizer1(mapper) o substsLogger(mapper) o boundT)(facts, tp); 
			return bound_ub0(facts, mapper, v); });
public BLogger[Entity] bound_ub0(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _, _, _) ])) // Ta -> Ta_ub
	= bind((parameterizer2(boundTa_ub0))(facts, mapper, entity(ta.id /*+ upper()*/)), BLogger[Entity] (Entity v) {
			return bound_ub0(facts, mapper, v); });
public BLogger[Entity] bound_ub0(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _, _, _), upper() ])) 
	= bind((parameterizer2(boundTa_ub0))(facts, mapper, ta), BLogger[Entity] (Entity v) {
			return bound_ub0(facts, mapper, v); });
public BLogger[Entity] bound_ub0(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _, _, _), lower() ])) 
	= bind((parameterizer2(boundTa_ub0))(facts, mapper, ta), BLogger[Entity] (Entity v) {
			return bound_ub0(facts, mapper, v); });
public default BLogger[Entity] bound_ub0(CompilUnit facts, Mapper mapper, Entity val) = returnBL(val);

@doc{Extended bound semantics against 'type environment' + 'substitutions'}
public BLogger[Entity] bound_lb(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str _) ])) 
	= bind(boundTSubsts_lb(facts, mapper, tp), BLogger[Entity] (Entity v) { return bound_lb(facts, mapper, v); });
public BLogger[Entity] bound_lb(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _, _, _) ]))  // Ta -> Ta_lb
	= bind((parameterizer2(boundTa_lb))(facts, mapper, entity(ta.id /*+ lower()*/)), BLogger[Entity] (Entity v) { 
			return bound_lb(facts, mapper, v); });
public BLogger[Entity] bound_lb(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _, _, _), upper() ])) 
	= bind((parameterizer2(boundTa_lb))(facts, mapper, ta), BLogger[Entity] (Entity v) { return bound_lb(facts, mapper, v); });
public BLogger[Entity] bound_lb(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _, _, _), lower() ])) 
	= bind((parameterizer2(boundTa_lb))(facts, mapper, ta), BLogger[Entity] (Entity v) { return bound_lb(facts, mapper, v); });
public default BLogger[Entity] bound_lb(CompilUnit facts, Mapper mapper, Entity val) = returnBL(val);

@doc{Extended bound semantics against 'type environment' + 'substitutions'}
public BLogger[Entity] boundUB(CompilUnit facts, Mapper mapper, Entity val) 
	= bind(boundTSubsts_ub(facts, mapper, val), BLogger[Entity] (Entity v) {
								if(v == zero()) return (parameterizer1(mapper) o substsLogger(mapper) o boundT)(facts, val);
								//if(isTypeArgument(v)) return returnBL(getUpperB(v)); 							 // Ta -> Ta_ub
								return returnBL(v); });
@doc{Extended bound semantics against 'type environment' + 'substitutions'}
public BLogger[Entity] boundLB(CompilUnit facts, Mapper mapper, Entity val) 
	= bind(boundTSubsts_lb(facts, mapper, val), BLogger[Entity] (Entity v) {
			//if(isTypeArgument(v)) return returnBL(getLowerB(v));												// Ta -> Ta_lb
			return returnBL(v); });

public BLogger[Entity] (CompilUnit, Mapper, Entity) parameterizer2(BLogger[Entity] (CompilUnit, Mapper, Entity) super) 
	= BLogger[Entity] (CompilUnit facts, Mapper mapper, Entity val) {
		BLogger[Entity] b = super(facts, mapper, val); 
		if(isTypeArgument(val))
			return bind(log(parameterize(mapper, evalb(b), val)), BLogger[Entity] (value _) {
						return returnBL(eval(b)); });
		return b; 
	  };
public BLogger[Entity] (CompilUnit, Entity) (BLogger[Entity] (CompilUnit, Entity)) parameterizer1(Mapper mapper) 
	= BLogger[Entity] (CompilUnit, Entity) (BLogger[Entity] (CompilUnit, Entity) super) {
		return BLogger[Entity] (CompilUnit facts, Entity val) {
			BLogger[Entity] b = super(facts, val); 
			if(isTypeParameter(val))
				return bind(log(parameterize(mapper, evalb(b), val)), BLogger[Entity] (value _) {
							return returnBL(eval(b)); });
			return b; 
	  }; };

@doc{ bound Ta ub and lb '+' Ta_lb '+' Ta_ub}
public BLogger[Entity] boundTa_ub(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_,_), upper()])) // '+' Ta_ub
	= boundTa_ub(facts, mapper, entity(ids + ta));
public BLogger[Entity] boundTa_ub(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_,_), lower()])) // '+' Ta_lb
	= boundTa_lb(facts, mapper, entity(ids + ta));
public BLogger[Entity] boundTa_ub(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str name, _, PEntity init) ])) 
	= bind(boundTa_ub0(facts, mapper, ta), BLogger[Entity] (Entity v) {
				if(v == zero()) {
					PEntity b = mkSubstsExplicit(mapper, eval(boundT(facts, entity([typeParameter(name)]))));
					return bind(log(bindings([ pzero() | Entity _ <- b.bindings.params ], b.bindings.params)), BLogger[Entity] (value _) { return returnBL(b@paramval); });
				} else return returnBL(v); }); 
public default BLogger[Entity] boundTa_ub(CompilUnit facts, Mapper mapper, Entity val) = returnBL(val);

public BLogger[Entity] boundTa_ub0(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_,_), upper()])) // '+' Ta_ub
	= boundTa_ub0(facts, mapper, entity(ids + ta));
public BLogger[Entity] boundTa_ub0(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_,_), lower()])) // '+' Ta_lb
	= boundTa_lb(facts, mapper, entity(ids + ta));
public BLogger[Entity] boundTa_ub0(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str name, _, PEntity init) ])) {
	if(isWildCardType(init.genval)) {
		BLogger[Entity] b = substsLogger(mapper)(boundWildcardUB)(facts, init.genval);
		if(eval(b) == zero()) init = pzero();
		else return b;
	}
	if(init == pzero()) 
		return returnBL(zero());
	return boundTa(facts, mapper, ta);
}
public default BLogger[Entity] boundTa_ub0(CompilUnit facts, Mapper mapper, Entity val) = returnBL(val);

public BLogger[Entity] boundTa_lb(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_,_), upper()])) // '+' Ta_ub
	= boundTa_lb(facts, mapper, entity(ids + ta));
public BLogger[Entity] boundTa_lb(CompilUnit facts, Mapper mapper, entity([ *ids, ta:typeArgument(str _,_,_), lower()])) // '+' Ta_lb 
	= boundTa_lb(facts, mapper, entity(ids + ta));
public BLogger[Entity] boundTa_lb(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str name, _, PEntity init) ])) {
	if(isWildCardType(init.genval)) {
		BLogger[Entity] b = substsLogger(mapper)(boundWildcardLB)(facts, init.genval);
		return b;
	}
	if(init == pzero()) return returnBL(zero());
	return boundTa(facts, mapper, ta);
}
public default BLogger[Entity] boundTa_lb(CompilUnit facts, Mapper mapper, Entity val) = returnBL(val);

public BLogger[Entity] boundTa(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str name, _, PEntity init)]))
	= bind(log(init.bindings), BLogger[Entity] (value _) { return returnBL(init@paramval); });
public default BLogger[Entity] boundTa(CompilUnit facts, Mapper mapper, Entity val) = returnBL(val);

@doc{ bound ^ T _ [./.] upper }
public BLogger[Entity] boundTSubsts_ub(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str _) ])) {
	return bind(boundTSubsts(facts, mapper, tp), BLogger[Entity] (Entity v) {
						return boundTSubsts_ub(facts, mapper, v); // =>recursion
				  });
}
public default BLogger[Entity] boundTSubsts_ub(CompilUnit facts, Mapper mapper, Entity val) {
	if(isWildCardType(val)) {
		return bind(substsLogger(mapper)(boundWildcardUB)(facts, val), BLogger[Entity] (Entity v) {
				return boundTSubsts_ub(facts, mapper, v); }); // =>recursion
	}
	return returnBL(val);
}
@doc{ bound ^ T _ [./.] lower }
public BLogger[Entity] boundTSubsts_lb(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str _) ])) {
	return bind(boundTSubsts(facts, mapper, tp), BLogger[Entity] (Entity v) {
						return boundTSubsts_lb(facts, mapper, v); // =>recursion
				  });
}
public default BLogger[Entity] boundTSubsts_lb(CompilUnit facts, Mapper mapper, Entity val) {
	if(isWildCardType(val)) {
		return bind(substsLogger(mapper)(boundWildcardLB)(mapper, val), BLogger[Entity] (Entity v) {
				return boundTSubsts_lb(facts, mapper, v); }); // =>recursion
	}
	return returnBL(val);
}

@doc{WILDCARDS: upper and lower bounds, respectively}
public BLogger[Entity] boundWildcardUB(CompilUnit facts, entity([ *ids, wildcard() ])) = returnBL(zero());
public BLogger[Entity] boundWildcardUB(CompilUnit facts, entity([ *ids, wildcard(extends(Entity wcb)) ])) = returnBL(wcb);
public BLogger[Entity] boundWildcardUB(CompilUnit facts, entity([ *ids, captureof(wildcard(extends(Entity wcb))) ])) = returnBL(wcb);
public BLogger[Entity] boundWildcardUB(CompilUnit facts, entity([ *ids, wildcard(super(Entity wcb)) ])) = returnBL(zero());
public BLogger[Entity] boundWildcardUB(CompilUnit facts, entity([ *ids, captureof(wildcard(super(Entity wcb))) ])) = returnBL(zero());

public BLogger[Entity] boundWildcardLB(CompilUnit facts, entity([ *ids, wildcard() ])) = returnBL(zero());
public BLogger[Entity] boundWildcardLB(CompilUnit facts, entity([ *ids, wildcard(super(Entity wcb)) ])) = returnBL(wcb);
public BLogger[Entity] boundWildcardLB(CompilUnit facts, entity([ *ids, captureof(wildcard(super(Entity wcb))) ])) = returnBL(wcb);
public BLogger[Entity] boundWildcardLB(CompilUnit facts, entity([ *ids, wildcard(extends(Entity wcb)) ])) = returnBL(zero());
public BLogger[Entity] boundWildcardLB(CompilUnit facts, entity([ *ids, captureof(wildcard(extends(Entity wcb))) ])) = returnBL(zero());

@doc{ bound ^ T _ [./.], may return 'zero' }
public BLogger[Entity] boundTSubsts(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str _)]))
	= bind(fetchBL(), BLogger[Entity] (Bindings bs) {
			PEntity b = lookupSubsts(bs, tp);
			if(tp == b.genval) return returnBL(tp);
			return bind(log(b.bindings), BLogger[Entity] (value _) {
						return boundTSubsts(facts, mapper, b@paramval); }); // =>recursion
			});
public default BLogger[Entity] boundTSubsts(CompilUnit facts, Mapper mapper, Entity val) = returnBL(val);

private PEntity lookupSubsts(Bindings bs, Entity val) {
	map[Entity, PEntity] mapOfbs = ();
	if(!isEmpty(bs.params))
		for(int i <- [0..size(bs.params) - 1])
			mapOfbs[bs.params[i]] = bs.args[i];
	return mapOfbs[val] ? pzero();
}
@doc{ bound ^ T _ TE }
@doc{Simple bound semantics against 'type environment'}
public BLogger[Entity] boundT(CompilUnit facts, tp:entity([ *ids, typeParameter(str name)])) {
	list[Entity] boundsOftp = typeParamBounds(facts, tp);
	map[Entity, Entity] mapOfbs = ();
	for(Entity tpb <- boundsOftp) mapOfbs[tp] = tpb;
	if(isEmpty(mapOfbs)) mapOfbs[tp] = object();
	Entity b = mapOfbs[tp];
	return boundT(facts, b); 	
}
public default BLogger[Entity] boundT(CompilUnit facts, Entity val) = returnBL(val);

public BLogger[Entity] (CompilUnit, Entity) (BLogger[Entity] (CompilUnit, Entity)) substsLogger(Mapper mapper) {
	return BLogger[Entity] (CompilUnit, Entity) (BLogger[Entity] (CompilUnit, Entity) super) {
			return BLogger[Entity] (CompilUnit facts, Entity val) {
				return bind(super(facts, val), BLogger[Entity] (Entity b) { 
						Bindings logbs = mkSubstsExplicit(mapper, b).bindings;
						return bind(log(logbs), BLogger[Entity] (value _) { return returnBL(b); }); }); 
			};
	};
}

public BLogger[Entity] parameterize(Mapper mapper, Entity val, AstNode t) {
	PEntity pval = mkSubstsExplicit(mapper, val);
	if(pval.bindings == bindings([],[])) return returnBL(val);
	list[Entity] params_ = getGenericTypes(pval.genval);
	if(isEmpty(params_)) return returnBL(val);
	list[Entity] params = pval.bindings.params;
	list[PEntity] args = pval.bindings.args;
	list[PEntity] args_ = [ args[i]| int i <- [0..size(params) - 1], params[i] in params_ ];
	Bindings logbs = parameterize(mapper, bindings(args_, params_), t); // tracer(logbs != bindings([],[]), "param internals log: <prettyprint(logbs)>");
	return bind(log(logbs), BLogger[Entity] (value _) { return returnBL(val); });
}

@doc{Parameterizes substitutions}
public Bindings parameterize(Mapper mapper, Bindings bs, context) {
	if(size(bs.params) == size(bs.args) && isEmpty(bs.params)) return bs;
	list[PEntity] pargs = [ typeArgument(mapper, bs.params[i], bs.args[i], context) | int i <- [0..(size(bs.params) - 1)] ];
	return bindings(pargs, bs.params);
}

public PEntity typeArgument(Mapper mapper, tp:entity([ *ids, typeParameter(str name) ]), PEntity init, context)
	 = (isTypeParameter(init) || !hasRawTypeArgument(mapper, init)) ? init : pentity(entity([ typeArgument(name, context, init) ]))[@paramval=entity([ typeArgument(name, context, init) ])];

private bool hasRawTypeArgument(Mapper mapper, PEntity init) {
	if(init == pzero()) return true;
	if(isWildCardType(init.genval))
		init = mkSubstsExplicit(mapper, boundWcardUB(init.genval));
	if(PEntity arg <- init.bindings.args, arg == pzero() || hasRawTypeArgument(mapper, arg)) return true;
	return false;
}
private bool hasRawTypeArgument(Entity init) {
	if(init == zero()) return true;
	if(PEntity arg <- mkSubstsExplicit(mapper, init).bindings.args, arg == pzero() || hasRawTypeArgument(arg)) return true;
	return false;
}

@doc{Additional 'downcast check' semantics over type values}
public bool isDownCast(CompilUnit facts, Mapper mapper, t:castExpression(_, AstNode e)) {
	return eval((superTypesGens(mapper) o superTypes)(facts, getType(t), getType(e)));
}

@doc{A function that returns the lookup subterm}
public Option[AstNode] subterm(e:classInstanceCreation(none(),_,[],_,none())) = none();
public Option[AstNode] subterm(e:classInstanceCreation(some(AstNode expr),_,[],_,none())) = some(rmv(expr));
public Option[AstNode] subterm(e:classInstanceCreation(_,_,[],_,some(AstNode anonymClass))) = none(); 
public Option[AstNode] subterm(e:fieldAccess(AstNode expr,_)) = some(rmv(expr)); 
public Option[AstNode] subterm(e:methodInvocation(none(),_,_,_)) = some(thisExpression(none())[@bindings = ("typeBinding" : e@scope)]);
public Option[AstNode] subterm(e:methodInvocation(some(AstNode expr),_,_,_)) = some(rmv(expr));
public Option[AstNode] subterm(e:qualifiedName(AstNode qname,_)) = (isVariableBinding(lookup(e))) ? some(qname) : none(); 
public Option[AstNode] subterm(e:simpleName(_)) = (isFieldBinding(lookup(e)) && !isArrayType(getType(e))) ? some(thisExpression(none())[@bindings = ("typeBinding" : e@scope)]) : none();
public Option[AstNode] subterm(e:superConstructorInvocation(none(),_,_)) = some(thisExpression(none())[@bindings = ("typeBinding" : e@scope)]);
public Option[AstNode] subterm(e:superConstructorInvocation(some(AstNode expr),_,_)) = some(rmv(expr));
public Option[AstNode] subterm(e:superFieldAccess(none(),_)) = some(thisExpression(none())[@bindings = ("typeBinding" : e@scope)]);
public Option[AstNode] subterm(e:superFieldAccess(some(AstNode qualifier),_)) = some(qualifier); 
public Option[AstNode] subterm(e:superMethodInvocation(none(),_,_,_)) = some(thisExpression(none())[@bindings = ("typeBinding" : e@scope)]);
public Option[AstNode] subterm(e:superMethodInvocation(some(AstNode qualifier),_,_,_)) = some(qualifier); 
public default Option[AstNode] subterm(AstNode t) = none();

public AstNode rmv(parenthesizedExpression(AstNode expr)) = rmv(expr);
public default AstNode rmv(AstNode expr) = expr;
