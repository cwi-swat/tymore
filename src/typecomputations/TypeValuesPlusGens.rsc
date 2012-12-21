@doc{The module extends the domain of type values with explicit substitutions of parameterized types and type argument values}
module typecomputations::TypeValuesPlusGens

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;
import lang::java::jdt::refactorings::PrettyPrintUtil;
import lang::java::jdt::refactorings::ValuesUtil;

import typecomputations::TypeValues;

import Prelude;


@doc{Entends the override semantics with the parameterized type semantics}
public set[PEntity] overrides(CompilUnit facts, Mapper mapper, PEntity val) = { toGens(mapper)(v) | Entity v <- overrides(facts, val@paramval) };
@doc{Extends the declaring type semantics with the parameterized type semantics}
public PEntity decl(PEntity val) = pentity(val.bindings, decl(val.genval))[@paramval=decl(val@paramval)];
@doc{Extends the declared parameter type semantics with the parameterized type semantics}
public PEntity param(PEntity val, int i) = pentity(val.bindings, param(val.genval, i))[@paramval=param(val@paramval, i)];
@doc{Additional 'declares' semantics over type values}
public set[PEntity] declares(CompilUnit facts, Mapper mapper, PEntity val) = { toGens(mapper)(v) | Entity v <- facts["declares_func"][val@paramval] };
@doc{Additional 'supertypes' semantics over type values}
public set[PEntity] supertypes(CompilUnit facts, Mapper mapper, PEntity val) = { toGens(mapper)(v) | Entity v <- facts["supertypes_func"][val@paramval]};
@doc{Additional 'downcast check' semantics over type values}
public bool isDownCast(CompilUnit facts, Mapper mapper, t:castExpression(_, AstNode e)) 
	= (toGens(mapper)(getType(e)) in supertypescls(facts, mapper, toGens(mapper)(getType(t)))) ? true : false
	;
public set[PEntity] supertypescls(CompilUnit facts, Mapper mapper, PEntity val) {
	set[PEntity] sups = supertypes(facts, mapper, val);
	return sups + { *supertypescls(facts, mapper, sup) | PEntity sup <- sups };
}
@doc{The evaluation semantics is extended with type argument semantics, i.e. the type argument values are introduced in place of types}	
public PEntity parameterize1(CompilUnit _, Mapper mapper, AstNode _, PEntity val1, PEntity val2) {	
	/* trace: */ tracer(false/*val2.bindings != bindings([],[])*/, "evalc + gens (in) : <prettyprint(val2)>;");
	if(val2.genval == val1.genval) return val1;
	if(val2.bindings == bindings([],[])) return pentity(val1.bindings, val2.genval)[@paramval=eval(val1@paramval)];	
	list[PEntity] args = val2.bindings.args;
	list[PEntity] bargs = toGens(mapper)(eval(val1@paramval)).bindings.args;
	list[Entity] params = val2.bindings.params;
	assert(size(args) == size(params));
	list[PEntity] pargs = [ typeArgument(args[i][@paramval=bargs[i]@paramval], params[i], val1.genval, mapper) | int i <- [0..(size(args) - 1)] ];	
	val2 = pentity(concat(val1.bindings, bindings(pargs, params)), val2.genval)[@paramval=eval(val1@paramval)];
	assert(size(pargs) == size(params));
	/* tracer: */ tracer(false/*val2.bindings != bindings([],[])*/, "evalc + gens (out) <prettyprint(val2)>; ");	
	return val2;
}	
public PEntity typeArgument(PEntity arg, tp:entity([ *ids, typeParameter(str name, list[Entity] bounds) ]), AstNode context, Mapper mapper) {
	if(isTypeParameter(arg)) return arg;
	return pentity(entity([ typeArgument(name, context, arg, [ toGens(mapper)(b) | Entity b <- bounds ]) ]))[@paramval=arg@paramval];
}
public PEntity typeArgument(PEntity arg, tp:entity([ *ids, typeParameter(str name, list[Entity] bounds) ]), Entity context, Mapper mapper) {
	if(isTypeParameter(arg)) return arg;
	return pentity(entity([ typeArgument(name, context, arg, [ toGens(mapper)(b) | Entity b <- bounds ]) ]))[@paramval=arg@paramval];
}
public PEntity parameterize2(CompilUnit facts, Mapper mapper, AstNode t, PEntity val1, PEntity val2) {
	/* trace: */ tracer(false/*val2.bindings != bindings([],[])*/, "parameterize lookup + gens (in) : <prettyprint(val1)> <prettyprint(val2)>; ");
	if(val2.bindings == bindings([],[])) return val2;				   
	list[Entity] termParams = getGenericTypes(val2.genval);
	list[PEntity] args = val2.bindings.args;
	list[Entity] params = val2.bindings.params;
	assert(size(args) == size(params));
	list[PEntity] pargs = [ typeArgument(args[i], params[i], t, mapper) | int i <- [0..(size(args) - 1)], params[i] in termParams ];
	assert(size(val1.bindings.args) == size(val1.bindings.params));
	PEntity bounded = bound(mapper, val1); 
	assert(size(bounded.bindings.args) == size(bounded.bindings.params));
	substs_sups = bindings(facts, mapper, toGens(mapper)(val1@paramval), val2); 
	assert(size(substs_sups.args) == size(substs_sups.params));
	val2 = pentity(concat(concat(bounded.bindings, substs_sups), bindings(pargs, termParams)), val2.genval)[@paramval=val2@paramval];
	/* trace: */ tracer(false/*val2.bindings != bindings([],[])*/, "parameterize lookup + gens (out) : <prettyprint(val2)>; <prettyprint(t)>");
	return val2;
}
public PEntity parameterize2(CompilUnit facts, Mapper mapper, AstNode t, PEntity val) {
	if(val.bindings == bindings([],[])) return val;
	list[Entity] termParams = getGenericTypes(val.genval);
	list[PEntity] args = val.bindings.args;
	list[Entity] params = val.bindings.params;
	assert(size(args) == size(params));
	list[PEntity] pargs = [ typeArgument(args[i], params[i], t, mapper) | int i <- [0..(size(args) - 1)], params[i] in termParams ];
	assert(size(pargs) == size(termParams));	
	return pentity(concat(val.bindings, bindings(pargs, termParams)), val.genval)[@paramval=val@paramval];
}
@doc{Expand the case of ([.], [.]) T}
public PEntity tpbound(Mapper mapper, pe:pentity(Bindings bs, tp:entity([ *ids, typeParameter(str name, list[Entity] bounds)]))) {
	/* tracer: */ tracer(false, "tpbound: <prettyprint(pe)>");
	map[Entity, PEntity] mapOfBindings = (!isEmpty(bs.params)) ? ( bs.params[i] : bs.args[i] | int i <- [0..size(bs.params) - 1] ) : ();
	PEntity b = mapOfBindings[tp] ? ( (!isEmpty(bounds)) ? toGens(mapper)(bounds[0]) : pobject());
	/* tracer: */ tracer(false, "tpbound bounded: <prettyprint(b)>");
	return tpbound(mapper, pentity(concat(bs, b.bindings), b.genval)[@paramval=b@paramval]); // NOTE: does not explicitly require pe@paramval
}
public PEntity tpbound(Mapper mapper, PEntity pe) = pe;

@doc{Deep lookup for a bound in case of ([.], [.]) T}
public PEntity bound(Mapper mapper, pe:pentity(Bindings bs, tp:entity([ *ids, typeParameter(str name, list[Entity] bounds)]))) {
	map[Entity, PEntity] mapOfBindings = (!isEmpty(bs.params)) ? ( bs.params[i] : bs.args[i] | int i <- [0..size(bs.params) - 1] ) : ();
	PEntity b = mapOfBindings[tp] ? ( (!isEmpty(bounds)) ? toGens(mapper)(bounds[0]) : pobject());
	assert(pe@paramval == b@paramval); // pe@paramval == b@paramval should be true by construction
	return bound(mapper, pentity(concat(bs, b.bindings), b.genval)[@paramval=pe@paramval]); 
}
public PEntity bound(Mapper mapper, pe:pentity(Bindings bs, tp:entity([ *ids, typeArgument(str name, context, PEntity init, list[PEntity] bounds) ]))) {
	PEntity b = (init == pzero()) ? ( (!isEmpty(bounds)) ? bounds[0] : pobject() ) : init ;
	if(b.bindings == bindings([],[])) { tracer(false, "it needs to be bound further <prettyprint(pentity(concat(bs, b.bindings), b.genval)[@paramval=pe@paramval])>"); return bound(mapper, pentity(concat(bs, b.bindings), b.genval)[@paramval=b@paramval]); }
	list[PEntity] args = b.bindings.args;
	list[Entity] params = b.bindings.params;
	list[PEntity] pargs = [ typeArgument(args[i], params[i], tp, mapper) | int i <- [0..size(args) - 1] ];
	assert(size(pargs) == size(params));
	/* trace: */ tracer(false, "Nested semantics : <prettyprint(bindings(pargs, params))>");
	return bound(mapper, pentity(concat(bs, bindings(pargs, params)), b.genval)[@paramval=pe@paramval]); // pe@paramval == init@paramval by construction
}
public PEntity bound(Mapper mapper, pe:pentity(Bindings bs, wcard:entity([ *ids, wildcard() ]))) = pobject();
public PEntity bound(Mapper mapper, pe:pentity(Bindings bs, entity([ *ids, wildcard(extends(Entity b)) ]))) {
	/* tracer */ tracer(true, "WILD CARD BOUND pe: <prettyprint(pe)> and its paramval: <prettyprint(pe@paramval)>");
	PEntity bounded = toGens(mapper)(b);
	if(entity([ *ids, wildcard(extends(Entity bb)) ]) := pe@paramval) {
		PEntity pe1 = pentity(concat(bs, bounded.bindings), bounded.genval)[@paramval=bb];
		/* tracer */ tracer(true, "WILD CARD BOUNDED pe1: <prettyprint(pe1)> and its paramval: <prettyprint(pe1@paramval)>");
		return pe1;
	}
	else throw "Problems with propagating paramval";
}
public PEntity bound(Mapper mapper, pe:pentity(Bindings bs, entity([ *ids, captureof(Entity b) ]))) {
	PEntity bounded = toGens(mapper)(b);
	if(entity([ *ids, captureof(Entity bb) ]) := pe@paramval)
		return bound(mapper, pentity(concat(bs, bounded.bindings), bounded.genval)[@paramval=bb]);
	else throw "Problems with propagating paramval";
}
public default PEntity bound(_, PEntity val) = val;

private Bindings bindings(CompilUnit facts, Mapper mapper, PEntity val1, PEntity val2) {	
	PEntity psup = (sup <- supertypes(facts, mapper, val1) && (val2 in declares(facts, mapper, sup))) ? sup : pzero();
	PEntity gsup = (sup <- supertypes(facts, mapper, pentity(val1.genval)) && (sup.genval == psup.genval)) ? sup : pzero();
	list[PEntity] args = gsup.bindings.args;
	list[Entity] params = gsup.bindings.params;	
	list[PEntity] pargs = [];
	if(!isEmpty(args)) pargs = [ typeArgument(args[i], params[i], entity(val1.genval.id + inherits(gsup.genval)), mapper) | int i <- [0..size(args) - 1] ];
	assert(size(pargs) == size(params));			
	substs_sups = concat(bindings(pargs, params), (psup != pzero()) ? bindings(facts, mapper, psup, val2) : pzero().bindings);
	assert(size(substs_sups.args) == size(substs_sups.params));
	return substs_sups;	
}
public set[PEntity] supertypesAll(CompilUnit facts, Mapper mapper, PEntity val) {	
	set[PEntity] gsups = supertypes(facts, mapper, pentity(val.genval));
	set[PEntity] sups = {};
	for(PEntity gsup <- gsups) { 
		list[PEntity] args = gsup.bindings.args;
		list[Entity] params = gsup.bindings.params;	
		list[PEntity] pargs = [];
		if(!isEmpty(args)) pargs = [ typeArgument(args[i], params[i], entity(val.genval.id + inherits(gsup.genval)), mapper) | int i <- [0..size(args) - 1] ];
		assert(size(pargs) == size(params));	
		PEntity psup = pzero();
		psup = if(s <- supertypes(facts, mapper, toGens(mapper)(val@paramval)) && (s.genval == gsup.genval)) s;
		PEntity sup = pentity(concat(val.bindings, bindings(pargs, params)), gsup.genval)[@paramval=psup@paramval];
		sups = sups + sup;
	}
	return sups + { *supertypesAll(facts, mapper, sup) | PEntity sup <- sups };	
}

/*
public bool isGenericDecl(PEntity val) {
			if(entity([ *ids,_ ]) := val.genval && id <- ids , ( class(_,_) := id || interface(_,_) := id ) ) return true;
			if(entity([ *ids, method(list[Entity] genericTypes,_,_,_)]) := val.genval || entity([ *ids, constr(list[Entity] genericTypes,_)]) := val.genval)
				return true;
			return false;
}

public bool (PEntity) isParamDeclaredType(Mapper mapper) 
	= bool (PEntity val) {
			if(isType(val.genval)) return true;
			if(entity([ *ids,_ ]) := val.genval && id <- ids , ( class(_,_) := id || interface(_,_) := id ) ) return false;
			if(entity([ *ids, method(list[Entity] genericTypes,_,_,_)]) := val.genval || entity([ *ids, constr(list[Entity] genericTypes,_)]) := val.genval)
				return false;
			if(/PEntity(bindings([],[]), entity([])) <- toGens(mapper)(eval(val)).bindings.args) return false;
			return true;
	};
*/	