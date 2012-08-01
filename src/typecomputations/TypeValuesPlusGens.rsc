/*
 * The module extends the domain of type values with :
 * - explicit substitutions of parameterized types and type argument values; and
 * - extra functional semantics
 */
module typecomputations::TypeValuesPlusGens

import List;
import Node;
import Relation;
import Set;

import lang::java::jdt::Java;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::JavaADT;

import typecomputations::TypeValues;
import typecomputations::TypeComputations;

import IO;

@doc{Extends the lookup semantics with the parameterized type semantics}
public ParameterizedEntity (AstNode) lookup(Mapper mapper) 
	= ParameterizedEntity (AstNode t) { return toGens(mapper)(lookup(t)); };
@doc{Extends the evaluation semantics with the parameterized type semantics}																		
public ParameterizedEntity (ParameterizedEntity) eval(Mapper mapper) 
	= ParameterizedEntity (ParameterizedEntity val) { 
		ParameterizedEntity v = toGens(mapper)(eval(val.genval)); 
		return pentity(concat(val.bindings, v.bindings), v.genval); 
	};
@doc{Entends the override semantics with the parameterized type semantics}
public set[ParameterizedEntity] (ParameterizedEntity) overrides(CompilUnitGens facts) 
	= set[ParameterizedEntity] (ParameterizedEntity val) { return toGens(facts.mapper)(facts.compilUnit["overrides_func"][val@paramval]); };
@doc{Extends the declaring type semantics with the parameterized type semantics}
public ParameterizedEntity decl(ParameterizedEntity val) = pentity(val.bindings, decl(val.genval));
@doc{Extends the declared parameter type semantics with the parameterized type semantics}
public ParameterizedEntity param(ParameterizedEntity val, int i) = pentity(val.bindings, param(val.genval, i));
@doc{Additional 'declares' semantics over type values}
set[ParameterizedEntity] (ParameterizedEntity) declares(CompilUnitGens facts) = set[ParameterizedEntity] (ParameterizedEntity val) { return toGens(facts.mapper)(facts.compilUnit["declares_func"][val@paramval]); };
@doc{Additional 'supertypes' semantics over type values}
set[ParameterizedEntity] (ParameterizedEntity) supertypes(CompilUnitGens facts) = set[ParameterizedEntity] (ParameterizedEntity val) { return toGens(facts.mapper)(facts.compilUnit["supertypes_func"][val@paramval]); };		

@doc{Recursive function that maps to the representation with explicit type parameter substitution}	
public ParameterizedEntity (Entity) toGens(Mapper mapper) 
	= ParameterizedEntity (Entity val) { 
		if(entity([ *ids, anonymous(_,_)]) := val) return pentity(val);
		tuple[tuple[list[Entity], list[Entity]], Entity] v = mapper[val];
		list[Entity] args = v[0][0];
		list[Entity] params = v[0][1];
		list[ParameterizedEntity] pArgs = (!isEmpty(params)) ? [ (entity([]) := args[i]) ? zero : toGens(mapper)(args[i])
																| int i <- [0..(size(params) - 1)] ] : [];
		return pentity(bindings(pArgs, params), v[1])[@paramval=val]; 
	};
	
public Bindings concat(Bindings b1, Bindings b2) { 
		assert(size(b1.args) == size(b1.params)); 
		assert(size(b2.args) == size(b2.params));	
		bs = bindings( ((!isEmpty(b1.params)) ? [ b1.args[i] | int i <- [0..size(b1.params)-1], b1.params[i] notin b2.params ] : []) + b2.args, 
			    	   ((!isEmpty(b1.params)) ? [ b1.params[i] | int i <- [0..size(b1.params)-1], b1.params[i] notin b2.params ] : []) + b2.params );
		assert(size(bs.args) == size(bs.params));
		return bs;
}
		
@doc{The evaluation semantics is extended with type argument semantics, i.e. the type argument values are introduced in place of types}	
public ParameterizedEntity (ParameterizedEntity) parameterize1(CompilUnitGens facts) 
	= ParameterizedEntity (ParameterizedEntity val) {	
		/* trace: */ tracer(val.bindings != bindings([],[]), "evalc + gens (in) : <prettyprint(val)>;");
		Entity context = val.genval;
		if(val == eval(facts.mapper)(val)) return val;
		val = eval(facts.mapper)(val);
		if(val.bindings == bindings([],[])) return val;	
		set[Entity] tps = { tp | /tp:entity([ *ids, typeParameter(_,_) ]) <- val.genval };
		list[ParameterizedEntity] args = val.bindings.args;
		list[Entity] params = val.bindings.params;
		assert(size(args) == size(params));
		list[ParameterizedEntity] pArgs = [ (params[i] in tps) ? typeArgument(args[i], params[i], context, facts.mapper) : args[i] 
											| int i <- [0..(size(args) - 1)] ];	
		val = pentity(bindings(pArgs, params), val.genval);
		assert(size(pArgs) == size(params));
		tracer(val.bindings != bindings([],[]), "evalc + gens (out) <prettyprint(val)>; ");	
		return val;
	};
	
@doc{ Evaluation under parameterization }
public  ParameterizedEntity (ParameterizedEntity) evalPlusGens(CompilUnitGens facts) = parameterize1;

public ParamterizedEntity typeArgument(ParameterizedEntity arg, tparam:entity([ *ids, typeParameter(str name, list[Entity] bounds) ]), &V context, Mapper mapper) {
	if(isTypeParameter(arg)) return arg;
	return pentity(entity([ typeArgument(name, context, arg, [ toGens(mapper)(b) | b <- bounds ]) ]));
}

public ParameterizedEntity (AstNode, AstNode, ParameterizedEntity, ParameterizedEntity) parameterize2(CompilUnitGens facts) 
	= ParameterizedEntity (AstNode term, AstNode subterm, ParameterizedEntity val, ParameterizedEntity tval) {
		/* trace: */ tracer(val.bindings != bindings([],[]), "parameterize lookup + gens (in) : <prettyprint(val)>; ");				   
		list[Entity] termParams = getGenericTypes(val.genval);
		list[ParameterizedEntity] args = val.bindings.args;
		list[Entity] params = val.bindings.params;
		assert(size(args) == size(params));
		list[ParameterizedEntity] pArgs = [];
		if(!isEmpty(args)) pArgs = [ typeArgument(args[i], params[i], term, facts.mapper) | int i <- [0..(size(args) - 1)], params[i] in termParams ];
		assert(size(tval.bindings.args) == size(tval.bindings.params));
		substs_bounds = bound(tval, facts.mapper);
		assert(size(substs_bounds.args) == size(substs_bounds.params));
		substs_sups = bindings(o(lookup(facts.mapper)(subterm), eval(facts.mapper)), val, facts); 
		assert(size(substs_sups.args) == size(substs_sups.params));
		val = pentity(concat(concat(concat(tval.bindings, substs_bounds), substs_sups), bindings(substs_sups, termParams)), val.genval);
		/* trace: */ tracer(val.bindings != bindings([],[]), "parameterize lookup + gens (out) : <prettyprint(val)>; <prettyprint(term)>");
		return val;
	};
	
public ParameterizedEntity (AstNode, ParameterizedEntity) parameterize2Reduced(CompilUnitGens facts) =
	ParameterizedEntity (AstNode term, ParameterizedEntity val) {
		list[Entity] termParams = getGenericTypes(val.genval);
		list[ParameterizedEntity] args = val.bindings.args;
		list[Entity] params = val.bindings.params;
		assert(size(args) == size(params));
		list[ParameterizedEntity] pArgs = [];
		if(!isEmpty(args)) pArgs = [ typeArgument(args[i], params[i], term, facts.mapper) | int i <- [0..(size(args) - 1)], params[i] in termParams ];
		assert(size(pArgs) == size(termParams));	
		return pentity(concat(val.bindings, bindings(pArgs, termParams)), val.genval);
	};
/*
 *	Looks up for a bound in case of ([.], [.]) T
 */
private Bindings bound(pentity(Bindings bs, tparam:entity([ *ids, typeParameter(str name, list[Entity] bounds)])), Mapper mapper) {
	map[Entity, ParameterizedEntity] mapOfBindings = (!isEmpty(bs.params)) ? ( bs.params[i] : bs.args[i] | int i <- [0..size(bs.params) - 1] ) : ();
	ParameterizedEntity b = mapOfBindings[tparam] ? ( (!isEmpty(bounds)) ? toGens(mapper)(bounds[0]) : object);
	return bound(pentity(concat(bs, b.bindings), b.genval), mapper);
}
private Bindings bound(pentity(Bindings bs, val:entity([ *ids, typeParameter(str name, context, ParameterizedEntity init, list[ParameterizedEntity] bounds) ])), Mapper mapper) {
	ParameterizedEntity b = (init == zero) ? ( (!isEmpty(bounds)) ? bounds[0] : object ) : init ;
	if(b.bindings == bindings([],[])) return bound(pentity(concat(bs, b.bindings), b.genval), mapper);
	list[ParameterizedEntity] args = b.bindings.args;
	list[Entity] params = b.bindings.params;
	list[ParameterizedEntity] pArgs = [];
	if(!isEmpty(args)) pArgs = [ typeArgument(args[i], params[i], val, mapper) | int i <- [0..size(args) - 1] ];
	assert(size(parameterizedArgs) == size(params));
	/* trace: */ tracer(true, "Nested sematics : <prettyprint(bindings(pArgs, params))>");
	return bound(pentity(concat(bs, bindings(pArgs, params)), b.genval), mapper);
}
private Bindings bound(pentity(Bindings bs, wcard:entity([ *ids, wildcard() ])), Mapper mapper) = bindings([], []);
private Bindings bound(pentity(Bindings bs, entity([ *ids, wildcard(extends(Entity b)) ])), Mapper mapper) = toGens(b).bindings;
private Bindings bound(pentity(Bindings bs, entity([ *ids, captureof(Entity b) ])), Mapper mapper) = bound(pentity(bs, b), mapper);
private default Bindings bound(ParameterizedEntity val, _) = val.bindings;

private Bindings bindings(ParameterizedEntity tval, ParameterizedEntity val, CompilUnitGens facts) {						
	ParameterizedEntity pSup = (sup <- supertypes(facts)(tval) && val in declares(facts)(sup)) ? sup : zero;
	ParameterizedEntity gSup = (sup <- supertypes(facts)(pentity(tval.genval)) && sup.genval == pSup.genval) ? sup : zero;
	list[ParameterizedEntity] args = gSup.bindings.args;
	list[Entity] params = gSup.bindings.params;	
	list[ParameterizedEntity] pArgs = [];
	if(!isEmpty(args)) pArgs = [ typeArgument(args[i], params[i], entity(tval.genval.id + inherits(gSup.genval)), facts.mapper) | int i <- [0..size(args) - 1] ];
	assert(size(pArgs) == size(params));			
	substs_sups = concat(bindings(pArgs, params), (pSup != zero) ? bindings(pSup, val, facts) : zero.bindings);
	assert(size(substs_sups.args) == size(substs_sups.params));
	return substs_sups;	
}

public bool isGenericDecl(ParameterizedEntity val) {
			if(entity([ *ids,_ ]) := val.genval && id <- ids , ( class(_,_) := id || interface(_,_) := id ) ) return true;
			if(entity([ *ids, method(list[Entity] genericTypes,_,_,_)]) := val.genval || entity([ *ids, constr(list[Entity] genericTypes,_)]) := val.genval)
				return true;
			return false;
}

public bool (ParameterizedEntity) isParamDeclaredType(Mapper mapper) 
	= bool (ParameterizedEntity val) {
			if(isType(val.genval)) return true;
			if(entity([ *ids,_ ]) := val.genval && id <- ids , ( class(_,_) := id || interface(_,_) := id ) ) return false;
			if(entity([ *ids, method(list[Entity] genericTypes,_,_,_)]) := val.genval || entity([ *ids, constr(list[Entity] genericTypes,_)]) := val.genval)
				return false;
			if(/parameterizedentity(bindings([],[]), entity([])) <- eval(mapper)(val).bindings.args) return false;
			return true;
	};
	
public void tracer(bool condition, str msg) {
	if(condition) println("TRACER: " + msg);
}