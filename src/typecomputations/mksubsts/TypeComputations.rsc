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


public BLogger[Entity] lookup_(CompilUnit facts, Mapper mapper, AstNode t) 
	= bind( lookup_(t), BLogger[Entity] (Entity val) {
							BLogger[Entity] subTypeLookupLog 
								= some(AstNode subt) := subterm(t) ? lookup_(facts, mapper, subt) 
																   : returnBL(zero()); 
							BLogger[Entity] (Entity) eval__ = evalLogger(mapper) o eval_;
							BLogger[bool] (CompilUnit, Entity, Entity) supertypes_ = superTypesLogger(mapper) o superTypes;
							return bind(bind(lookup_(t), BLogger[Entity] (Entity v) { 
											return bind(subTypeLookupLog, BLogger[Entity] (Entity v1) { 
															if(v1 == zero()) 
																return returnBL(v);
															return bind(eval__(v1), BLogger[Entity] (Entity v2) {
																		return bind(bound_(facts, mapper, eval(mkSubstsExplicit(mapper, v1).genval)), BLogger[Entity] (Entity _) {
																					return bind(supertypes_(facts, v2, eval(decl(v))), BLogger[Entity] (bool _) {
																								return returnBL(v); }); }); }); }); }),
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
			Bindings logbs = (genval != eval(genval)) ? parameterize(mkSubstsExplicit(mapper, eval(genval)).bindings, genval)
													  : bindings([],[]);
			// tracer(logbs != bindings([],[]), "eval log: <prettyprint(val)> - <prettyprint(logbs)>");
			return bind(log(logbs), BLogger[Entity] (value _) { return super(val); });
		};
	};
}

public list[Entity] supertypes(CompilUnit facts, Entity val) = [ sup | Entity sup <- facts["supertypes_func"][val]];
public list[Entity] typeParamBounds(CompilUnit facts, Entity val) = [ v | <Entity k, Entity v> <- facts["bounds_func"], k == val];

public BLogger[bool] superTypes(CompilUnit facts, Entity rtype, Entity dtype) {
	if(rtype == dtype) 
		return returnBL(true);
	if(Entity sup <- supertypes(facts, rtype), 
	   BLogger[bool] isSup := superTypes(facts, sup, dtype), 
	   eval(isSup)) 
	   		return isSup;
	return returnBL(false);
}

public BLogger[bool] (CompilUnit, Entity, Entity) (BLogger[bool] (CompilUnit, Entity, Entity)) superTypesGens(Mapper mapper) {
	return BLogger[bool] (CompilUnit, Entity, Entity) (BLogger[bool] (CompilUnit, Entity, Entity) super) {
		return BLogger[bool] (CompilUnit facts, Entity rtype, Entity dtype) {
			if(mkSubstsExplicit(mapper, rtype).genval == mkSubstsExplicit(mapper, dtype).genval) {
				// tracer(true, "supertypes in presence of raw types: <prettyprint(rtype)> -- <prettyprint(dtype)>");
				return returnBL(true);
			}
			return super(facts, rtype, dtype);
		};
	};
}

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
		    		if(Entity supOfGen <- supertypes(facts, prtype.genval), 
		    		   PEntity psupOfGen := mkSubstsExplicit(mapper, supOfGen), 
		    		   psupOfGen.genval == psup.genval)
		    		   		logbs = parameterize(psupOfGen.bindings, inherits(prtype.genval, supOfGen));
		    	} 
		    	// tracer(logbs != bindings([],[]), "sup logbs: <prettyprint(logbs)>");
		    	sups = rtype + sups; 
		    }
		    return bind(log(logbs), BLogger[bool] (value _) { 
		    				return bind(prev, BLogger[bool] (bool b) { 
		    								return returnBL(b); }); });
		    return returnBL(true);
		};
	};
}

@doc{Extended bound semantics against 'type environment' + 'substitutions'}
public BLogger[Entity] bound_(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str _) ])) 
	= bind(boundTSubsts_(facts, mapper, tp), BLogger[Entity] (Entity v) {
								if(v == zero()) return (boundTLogger(mapper) o boundT)(facts, v);
								return bound_(facts, mapper, v); });
public BLogger[Entity] bound_(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _, _, _) ])) 
	= bind(boundTa_(facts, mapper, ta), BLogger[Entity] (Entity v) {
			return bound_(facts, mapper, v); });
public default BLogger[Entity] bound_(CompilUnit facts, Mapper mapper, Entity val) = returnBL(val);

@doc{Extended bound semantics against 'type environment' + 'substitutions'}
public BLogger[Entity] bound(CompilUnit facts, Mapper mapper, Entity val) 
	= bind(boundTSubsts(facts, mapper, val), BLogger[Entity] (Entity v1) {
								if(v1 == zero()) return (boundTLogger(mapper) o boundT)(facts, v1);
								return returnBL(v1); });

public BLogger[Entity] boundTa_(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str name, _, PEntity init)])) {	
	if(isWildCardType(init.genval)) {
		BLogger[Entity] b = boundWildcard(facts, mapper, init.genval);
		if(eval(b) == zero()) init = pzero();
		else return bind(log(parameterize(evalb(b), ta)), BLogger[Entity] (value _) { return returnBL(eval(b)); });
	}
	if(init == pzero()) {
		PEntity b = mkSubstsExplicit(mapper, eval(boundT(facts, entity([typeParameter(name)]))));
		Bindings logbs = parameterize(b.bindings, ta);
		return bind(log(logbs), BLogger[Entity] (value _) { return returnBL(b@paramval); });
	}
	return boundTa(facts, mapper, ta);
}
public default BLogger[Entity] boundTa_(CompilUnit facts, Mapper mapper, Entity val) = returnBL(val);

public BLogger[Entity] boundTa(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str name, _, PEntity init)])) {
	Bindings logbs = parameterize(init.bindings, ta);
	return bind(log(logbs), BLogger[Entity] (value _) {
					return returnBL(init@paramval); });
}
public default BLogger[Entity] boundTa(CompilUnit facts, Mapper mapper, Entity val) = returnBL(val);

public BLogger[Entity] boundWildcard(CompilUnit facts, Mapper mapper, entity([ *ids, wildcard() ])) = returnBL(zero());
public BLogger[Entity] boundWildcard(CompilUnit facts, Mapper mapper, entity([ *ids, wildcard(extends(Entity wcb)) ])) 
	= bind(boundWildcard(facts, mapper, wcb), BLogger[Entity] (Entity v) {
			Bindings logbs = mkSubstsExplicit(mapper, v).bindings;
			return bind(log(logbs), BLogger[Entity] (value _) {
							return returnBL(v); }); });
public BLogger[Entity] boundWildcard(CompilUnit facts, Mapper mapper, entity([ *ids, captureof(wildcard(extends(Entity wcb))) ]))
	= bind(boundWildcard(facts, mapper, wcb), BLogger[Entity] (Entity v) {
			Bindings logbs = mkSubstsExplicit(mapper, v).bindings;
			return bind(log(logbs), BLogger[Entity] (value _) {
							return returnBL(v); }); });
public default BLogger[Entity] boundWildcard(CompilUnit facts, Mapper mapper, Entity val) = returnBL(val);

@doc{Extended bound semantics against 'type environment' + 'substitutions'}
public BLogger[Entity] boundTSubsts_(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str _) ])) {
	return bind(boundTSubsts(facts, mapper, tp), BLogger[Entity] (Entity v) {
						return boundTSubsts_(facts, mapper, v); // =>recursion
				  });
}
public default BLogger[Entity] boundTSubsts_(CompilUnit facts, Mapper mapper, Entity val) {
	if(isWildCardType(val)) {
		return bind(boundWildcard(facts, mapper, val), BLogger[Entity] (Entity v) {
				return boundTSubsts_(facts, mapper, v); }); // =>recursion
	}
	return returnBL(val);
}

public BLogger[Entity] boundTSubsts(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str _)]))
	= bind(fetchBL(), BLogger[Entity] (Bindings bs) {
			PEntity b = lookupSubsts(bs, tp);
			if(tp == b.genval) return returnBL(tp);
			Bindings logbs = b.bindings;
			return bind(log(logbs), BLogger[Entity] (value _) {
						return boundTSubsts(facts, mapper, b@paramval); }); // the bound can be a type parameter (=>recursion)
			});
public default BLogger[Entity] boundTSubsts(CompilUnit facts, Mapper mapper, Entity val) = returnBL(val);

private PEntity lookupSubsts(Bindings bs, Entity val) {
	map[Entity, PEntity] mapOfbs = ();
	if(!isEmpty(bs.params))
		for(int i <- [0..size(bs.params) - 1])
			mapOfbs[bs.params[i]] = bs.args[i];
	return mapOfbs[val] ? pzero();
}

@doc{Simple bound semantics against 'type environment'}
public BLogger[Entity] boundT(CompilUnit facts, tp:entity([ *ids, typeParameter(str name)])) {
	list[Entity] boundsOftp = typeParamBounds(facts, tp);
	map[Entity, Entity] mapOfbs = ();
	for(Entity tpb <- boundsOftp)
		mapOfbs[tp] = tpb;
	if(isEmpty(mapOfbs))
		mapOfbs[tp] = object();
	Entity b = mapOfbs[tp];
	return boundT(facts, b); 	
}
public default BLogger[Entity] boundT(CompilUnit facts, Entity val) = returnBL(val);

@doc{Logger that extends simple bound semantics}
public BLogger[Entity] (CompilUnit, Entity) (BLogger[Entity] (CompilUnit, Entity)) boundTLogger(Mapper mapper) {
	return BLogger[Entity] (CompilUnit, Entity) (BLogger[Entity] (CompilUnit, Entity) super) {
			return BLogger[Entity] (CompilUnit facts, Entity val) {
				return bind(super(facts, val), BLogger[Entity] (Entity b) { 
						return bind((isTypeParameter(val) && !isTypeParameter(b)) 
														 ? log(parameterize(mkSubstsExplicit(mapper, b).bindings, val)) 
														 : log(bindings([],[])), 
									 BLogger[Entity] (value _) { return returnBL(b); }); }); 
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
	Bindings logbs = parameterize(bindings(args_, params_), t);
	// tracer(logbs != bindings([],[]), "param internals log: <prettyprint(logbs)>");
	return bind(log(logbs), BLogger[Entity] (value _) { return returnBL(val); });
}

@doc{Parameterizes substitutions}
public Bindings parameterize(Bindings bs, context) {
	if(size(bs.params) == size(bs.args) && isEmpty(bs.params)) return bs;
	list[PEntity] pargs = [ typeArgument(bs.params[i], bs.args[i], context) | int i <- [0..(size(bs.params) - 1)] ];
	return bindings(pargs, bs.params);
}

public PEntity typeArgument(tp:entity([ *ids, typeParameter(str name) ]), PEntity init, context)
	 = (isTypeParameter(init) || !hasRawTypeArgument(init)) ? init : pentity(entity([ typeArgument(name, context, init) ]))[@paramval=entity([ typeArgument(name, context, init) ])];

private bool hasRawTypeArgument(PEntity init) {
	if(init == pzero()) return true;
	if(PEntity arg <- init.bindings.args, arg == pzero() || hasRawTypeArgument(arg)) return true;
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

//@doc{Extended bound semantics against 'type environment' + 'substitutions'}
//public BLogger[Entity] bound(CompilUnit facts, Mapper mapper, tp:entity([ *ids, typeParameter(str _)])) {
//	return bind(fetchBL(), BLogger[Entity] (Bindings bs) {
//						return bind(parameterize(facts, mapper, bs, tp), BLogger[Entity] (Entity val) {
//									if(val == zero()) // <= a bound is not found in 'bs'
//										return (boundTLogger(mapper) o boundT)(facts, tp);
//									// => recursion (the bound can be a type argument constraint or type parameter again) 
//									return bound(facts, mapper, val); }); 
//				  });
//}
//
//@doc{Extended bound semantics against 'type environment' + 'substitutions'}
//public BLogger[Entity] bound(CompilUnit facts, Mapper mapper, ta:entity([ *ids, typeArgument(str _,_, PEntity _)])) {
//	return bind(fetchBL(), BLogger[Entity] (Bindings bs) {
//						return bind(parameterize(facts, mapper, bs, ta), BLogger[Entity] (Entity val) {
//									// => recursion (the bound can be a type argument constraint or type parameter again)
//									return bound(facts, mapper, val); }); 
//				  });
//}
//public default BLogger[Entity] bound(CompilUnit facts, Mapper mapper, Entity val) = returnBL(val);
//
//@doc{Parameterizes substitutions when handling with nesting}
//public BLogger[Entity] parameterize(CompilUnit facts, Mapper mapper, Bindings bs, tp:entity([ *ids, typeParameter(str _) ])) {
//	PEntity b = lookupSubsts(bs, tp);	
//	if(tp == b.genval) return returnBL(tp);
//	if(isTypeArgument(b)) return returnBL(b.genval);           // <= (1) the bound is a type argument constraint
//	if(isTypeParameter(b)) return returnBL(b.genval);          // <= (2) the bound is a type parameter
//	if(isWildCardType(b.genval))                               // <= (3) the bound is a wild card
//		b = mkSubstsExplicit(mapper, boundWildcard(b.genval)); 
//	Bindings logbs = b.bindings;
//	return bind(log(logbs), BLogger[Entity] (value _) { return returnBL(b@paramval); });
//}
//public BLogger[Entity] parameterize(CompilUnit facts, Mapper mapper, Bindings bs, ta:entity([ *ids, typeArgument(str name, _, PEntity init) ])) {
//	if(isWildCardType(init.genval))                                       // <= (1) the type argument is a wild card or capture 
//		init = mkSubstsExplicit(mapper, boundWildcard(init.genval));      //        it can return 'zero' for '?'
//	if(init == pzero())                                                   // <= (2) the type argument is of a raw type
//		init = mkSubstsExplicit(mapper, eval(boundT(facts, entity([typeParameter(name)]))));
//	Bindings logbs = parameterize(init.bindings, ta);
//	// tracer(logbs != bindings([],[]), "bounds log: <prettyprint(logbs)> -- <prettyprint(ta)> -- <prettyprint(bs)>");
//	return bind(log(logbs), BLogger[Entity] (value _) { return returnBL(init@paramval); });
//}
//public default BLogger[Entity] parameterize(CompilUnit facts, Mapper mapper, Bindings bs, Entity val) = returnBL(val);
