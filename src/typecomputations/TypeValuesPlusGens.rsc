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
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::JavaADT;

import typecomputationbasedframework4refactorings::TypeValues;
import typecomputationbasedframework4refactorings::TypeComputations;

import IO;

data Option[&V] = some(&B val)
				| none();  
				
public alias CompilUnitGens = map[str, rel[ParameterizedEntity, ParameterizedEntity]];

data Bindings = bindings(list[ParameterizedEntity] args, list[Entity] params);
data ParameterizedEntity = parameterizedentity(Bindings bindings, Entity genericval);  

/*
 * Helper functions
 */
public bool isTypeParameter(ParameterizedEntity val) = isTypeParameter(val.genericval);
public bool isTypeArgument(entity([ *ids, typeArgument(str name, context, ParameterizedEntity init, list[ParameterizedEntity] bounds) ])) = true;
public bool isTypeArgument(parameterizedentity(bindings([],[]), entity([ *ids, typeArgument(str name, context, ParameterizedEntity init, list[ParameterizedEntity] bounds) ]))) = true;
public bool isTypeArgument(_) = false;

@doc{Extends the lookup semantics with the parameterized type semantics}
public ParameterizedEntity (AstNode) lookup(ParameterizedEntity (Entity) toGens) 
	= ParameterizedEntity (AstNode t) { return toGens(lookup(t)); };
@doc{Extends the evaluation semantics with the parameterized type semantics}																		
public ParameterizedEntity (ParameterizedEntity) eval(ParameterizedEntity (Entity) toGens) 
	= ParameterizedEntity (ParameterizedEntity v) { 
		ParameterizedEntity genericval = toGens(eval(v.genericval)); return parameterizedentity(concat(v.bindings, genericval.bindings), genericval.genericval); 
	};
@doc{Entends the override semantics with the parameterized type semantics}
public set[ParameterizedEntity] (ParameterizedEntity) overrides(CompilUnitGens facts) 
	= set[ParameterizedEntity] (ParameterizedEntity val) { return facts["overrides_func"][val]; };
@doc{Extends the declaring type semantics with the parameterized type semantics}
public ParameterizedEntity decl(ParameterizedEntity val) = parameterizedentity(val.bindings, decl(val.genericval.id));
@doc{Extends the declared parameter type semantics with the parameterized type semantics}
public ParameterizedEntity param(ParameterizedEntity val, int i) = parameterizedentity(val.bindings, param(val.genericval.id, i));
@doc{Additional 'declares' semantics over type values}
set[ParameterizedEntity] (ParameterizedEntity) declares(CompilUnitGens facts) = set[ParameterizedEntity] (ParameterizedEntity val) { return facts["declares_func"][val]; };
@doc{Additional 'supertypes' semantics over type values}
set[ParameterizedEntity] (ParameterizedEntity) supertypes(CompilUnitGens facts) = set[ParameterizedEntity] (ParameterizedEntity val) { return facts["supertypes_func"][val]; };		

@doc{Recursive function that maps to the representation with explicit type parameter substitution}	
public ParameterizedEntity (Entity) toGens(tuple[ tuple[list[Entity], list[Entity]], Entity ] (Entity) mapper) 
	= ParameterizedEntity (Entity val) { 
		if(entity([ *ids, anonymous(_,_)]) := v) return parameterizedentity(val);
		tuple[tuple[list[Entity], list[Entity]], Entity] v = mapper(val);
		list[Entity] args = v[0][0];
		list[Entity] params = v[0][1];
		list[ParameterizedEntity] parameterizedArgs = (!isEmpty(params)) ? [ (entity([]) := args[i]) ? zero : toGens(mapper)(args[i])
															| int i <- [0..(size(params) - 1)] ] : [];
		return parameterizedentity(bindings(parameterizedArgs, params), v[1]); 
	};
	
public Bindings concat(Bindings b1, Bindings b2) { 
		assert(size(b1.args) == size(b1.params)); assert(size(b2.args) == size(b2.params));	
		bs = bindings( ((!isEmpty(b1.params)) ? [ b1.args[i] | int i <- [0..size(b1.params)-1], b1.params[i] notin b2.params ] : []) + b2.args, 
			    	   ((!isEmpty(b1.params)) ? [ b1.params[i] | int i <- [0..size(b1.params)-1], b1.params[i] notin b2.params ] : []) + b2.params );
		assert(size(bs.args) == size(bs.params));
		return bs;
}
		
@doc{The evaluation semantics is extended with type argument semantics, i.e. the type argument values are introduced in place of types}	
public ParameterizedEntity (ParameterizedEntity) parameterize1(ParameterizedEntity (Entity) toGens, CompilUnitGens facts) 
	= ParameterizedEntity (ParameterizedEntity val) {	
		tracer(val.bindings != bindings([],[]), "evalc + gens (in) : <prettyprint(val)>;");
		Entity context = val.genericval;
		if(val == eval(toGens)(val)) return val;
		val = eval(toGens)(val);
		if(val.bindings == bindings([],[])) return val;	
		set[Entity] tps = { tp | /tp:entity([ *ids, typeParameter(_,_) ]) <- val.genericval };
		list[ParameterizedEntity] args = val.bindings.args;
		list[Entity] params = val.bindings.params;
		assert(size(args) == size(params));
		list[ParameterizedEntity] parameterizedArgs = [ (params[i] in tps) ? typeArgument(args[i], params[i], context, toGens) : args[i] 
														| int i <- [0..(size(args) - 1)] ];	
		val = parameterizedentity(bindings(parameterizedArgs, params), val.genericval);
		assert(size(args_parameterized) == size(params));
		tracer(val.bindings != bindings([],[]), "evalc + gens (out) <prettyprint(val)>; ");	
		return val;
	};

public ParamterizedEntity typeArgument(ParameterizedEntity arg, tparam:entity([ *ids, typeParameter(str name, list[Entity] bounds) ]), &V context, ParameterizedEntity (Entity) toGens) {
	if(isTypeParameter(arg)) return arg;
	return parameterizedentity(entity([ typeArgument(name, context, arg, [ toGens(b) | b <- bounds ]) ]));
}

// public str getParamName(entity([ *ids, typeParameter(str name, _) ])) = name;
public ParameterizedEntity (AstNode, AstNode, ParameterizedEntity, ParameterizedEntity) parameterize2(ParameterizedEntity (Entity) toGens, CompilUnitGens facts) 
	= ParameterizedEntity (AstNode term, AstNode subterm, ParameterizedEntity val, ParameterizedEntity tval) {
		tracer(val.bindings != bindings([],[]), "parameterize lookup + gens (in) : <prettyprint(val)>; ");				   
		list[Entity] termParams = getGenericTypes(val.genericval);
		list[ParameterizedEntity] args = val.bindings.args;
		list[Entity] params = val.bindings.params;
		assert(size(args) == size(params));
		list[ParameterizedEntity] parameterizedArgs = [];
		if(!isEmpty(args)) parameterizedArgs = [ typeArgument(args[i], params[i], term, toGens) | int i <- [0..(size(args) - 1)], params[i] in termParams ];
		assert(size(tval.bindings.args) == size(tval.bindings.params));
		substs_bounds = bound(tval, toGens);
		assert(size(substs_bounds.args) == size(substs_bounds.params));
		substs_sups = bindings(o(lookup(toGens)(subterm), eval(toGens)), val, toGens, facts); 
		assert(size(substs_sups.args) == size(substs_sups.params));
		val = parameterizedentity(concat(concat(concat(tval.bindings, substs_bounds), substs_sups), bindings(substs_sups, termParams)), val.genericval);
		tracer(val.bindings != bindings([],[]), "parameterize lookup + gens (out) : <prettyprint(val)>; <prettyprint(term)>");
		return val;
	};
	
public ParameterizedEntity (AstNode, ParameterizedEntity) parameterize2_reduced(ParameterizedEntity (Entity) toGens, CompilUnitGens facts) =
	ParameterizedEntity (AstNode term, ParameterizedEntity val) {
		list[Entity] termParams = getGenericTypes(val.genericval);
		list[ParameterizedEntity] args = val.bindings.args;
		list[Entity] params = val.bindings.params;
		assert(size(args) == size(params));
		list[ParameterizedEntity] parameterizedArgs = [];
		if(!isEmpty(args)) parameterizedArgs = [ typeArgument(args[i], params[i], term, toGens) | int i <- [0..(size(args) - 1)], params[i] in termParams ];
		assert(size(parameterizedArgs) == size(termParams));	
		return parameterizedentity(concat(val.bindings, bindings(args_parameterized, termParams)), val.genericval);
	};
/*
 *	Looks up for a bound in case of ([.], [.]) T
 */
private Bindings bound(parameterizedentity(Bindings bs, tparam:entity([ *ids, typeParameter(str name, list[Entity] bounds)])), ParameterizedEntity (Entity) toGens) {
	map[Entity, ParameterizedEntity] mapOfBindings = (!isEmpty(bs.params)) ? ( bs.params[i] : bs.args[i] | int i <- [0..size(bs.params) - 1] ) : ();
	ParameterizedEntity b = mapOfBindings[tparam] ? ( (!isEmpty(bounds)) ? toGens(bounds[0]) : object);
	return bound(parameterizedentity(concat(bs, b.bindings), b.genericval), toGens);
}
private Bindings bound(parameterizedentity(Bindings bs, val:entity([ *ids, typeParameter(str name, context, ParameterizedEntity init, list[ParameterizedEntity] bounds) ])), ParameterizedEntity (Entity) toGens) {
	ParameterizedEntity b = (init == zero) ? ( (!isEmpty(bounds)) ? bounds[0] : object ) : init ;
	if(b.bindings == bindings([],[])) return bound(parameterizedentity(concat(bs, b.bindings), b.genericval), toGens);
	list[ParameterizedEntity] args = b.bindings.args;
	list[Entity] params = b.bindings.params;
	list[ParameterizedEntity] parameterizedArgs = [];
	if(!isEmpty(args)) parameterizedArgs = [ typeArgument(args[i], params[i], val, toGens) | int i <- [0..size(args) - 1] ];
	assert(size(parameterizedArgs) == size(params));
	tracer(true, "Nested sematics : <prettyprint(bindings(parameterizedArgs, params))>");
	return bound(parameterizedentity(concat(bs, bindings(parameterizedArgs, params)), b.genericval), toGens);
}
private Bindings bound(parameterizedentity(Bindings bs, wcard:entity([ *ids, wildcard() ])), ParameterizedEntity (Entity) toGens) = bindings([], []);
private Bindings bound(parameterizedentity(Bindings bs, entity([ *ids, wildcard(extends(Entity b)) ])), ParameterizedEntity (Entity) toGens) = toGens(b).bindings;
private Bindings bound(parameterizedentity(Bindings bs, entity([ *ids, captureof(Entity b) ])), ParameterizedEntity (Entity) toGens) = bound(parameterizedentity(bs, b), toGens);
private default Bindings bound(ParameterizedEntity val, _) = val.bindings;

private Bindings bindings(ParameterizedEntity tval, ParameterizedEntity val, ParameterizedEntity (Entity) toGens, CompilUnitGens facts) {						
	ParameterizedEntity parameterizedSup = (sup <- supertypes(toGens, facts)(tval) && val in declares(toGens, facts)(sup)) ? sup : zero;
	ParameterizedEntity genericSup = (sup <- supertypes(toGens, facts)(parameterizedentity(tval.genericval)) && sup.genericval == parameterizedSup.genericval) ? sup : zero;
	list[ParameterizedEntity] args = genericSup.bindings.args;
	list[Entity] params = genericSup.bindings.params;	
	list[ParameterizedEntity] parameterizedArgs = [];
	if(!isEmpty(args)) parameterizedArgs = [ typeArgument(args[i], params[i], entity(tval.genericval.id + inherits(genericSup.genericval)), toGens) | int i <- [0..size(args) - 1] ];
	assert(size(parameterizedArgs) == size(params));			
	substs_sups = concat(bindings(parameterizedArgs, params), (parameterizedSup != zero) ? bindings(parameterizedSup, val, toGens, facts) : zero.bindings );
	assert(size(substs_sups.args) == size(substs_sups.params));
	return substs_sups;	
}

public bool isGenericDecl(ParameterizedEntity val) {
			if(entity([ *ids,_ ]) := val.genericval && id <- ids , ( class(_,_) := id || interface(_,_) := id ) ) return true;
			if(entity([ *ids, method(list[Entity] genericTypes,_,_,_)]) := val.genericval || entity([ *ids, constr(list[Entity] genericTypes,_)]) := val.genericval)
				return true;
			return false;
}

public bool (ParameterizedEntity) isParamDeclaredType(ParameterizedEntity (Entity) toGens) 
	= bool (ParameterizedEntity val) {
			if(isType(val.genericval)) return true;
			if(entity([ *ids,_ ]) := val.genericval && id <- ids , ( class(_,_) := id || interface(_,_) := id ) ) return false;
			if(entity([ *ids, method(list[Entity] genericTypes,_,_,_)]) := val.genericval || entity([ *ids, constr(list[Entity] genericTypes,_)]) := val.genericval )
				return false;
			if(/parameterizedentity(bindings([],[]), entity([])) <- eval(toGens)(val).bindings.args) return false;
			return true;
	};
	
public void tracer(bool condition, str msg) {
	if(condition) println("TRACER: " + msg);
}