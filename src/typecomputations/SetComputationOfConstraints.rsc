module typecomputationbasedframework4refactorings::SetComputationOfConstraints

import List;
import Node;
import Relation;
import Set;

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::JavaADT;

import typecomputationbasedframework4refactorings::TypeValues;
import typecomputationbasedframework4refactorings::TypeComputations;
import typecomputationbasedframework4refactorings::TypeValuesPlusGens;
import typecomputationbasedframework4refactorings::TypeComputationsPlusGens;


import IO;


data Constraint[&B] = eq(&B lh, &B rh)
					  | subtype(&B lh, &B rh);

public set[Constraint[&B]] (AstNode) constraints(&B (AstNode) lookup_a_PlusGens, 
												 &B (AstNode) lookup_a_PlusGens_Open, 
												 &B (&V) filter_a_2, 
												 set[&V] (SetTypeOf[&V]) eval, 
												 &V (AstNode) lookup, 
												 &V (&V) evaluation_func,
												 set[&B] (&B) supertypes_func, 
												 set[Entity] (Entity) bounds_delta, 
												 ParameterizedEntity (Entity) toGenerics) 
	= set[Constraint[&B]] (AstNode t) { 
		
		// println("<prettyprint(t)>");
		
		cons = constraints_gens(t, lookup_a_PlusGens, lookup_a_PlusGens_Open, filter_a_2, lookup, evaluation_func, supertypes_func);
		
		set[Constraint[ParameterizedEntity]] IGTAsCons = {};
		
		for(c <- cons) 
			{ 
				switch(c) {
					case eq(v1, v2): IGTAsCons += closure(eq(getOneFrom(o(v1, eval)), getOneFrom(o(v2, eval))), supertypes_func, bounds_delta, toGenerics);
					case subtype(v1, v2): IGTAsCons += closure(subtype(getOneFrom(o(v1, eval)), getOneFrom(o(v2, eval))), supertypes_func, bounds_delta, toGenerics); 
				}
			};
		
		for(c <- IGTAsCons, c.lh != c.rh) if(isTypeArgumentVariable(c.lh) || isTypeArgumentVariable(c.rh)) {
			if(eq(_,_) := c) println("IGTAs specific: <prettyprint(c.lh)> = <prettyprint(c.rh)>");
			else println("IGTAs specific: <prettyprint(c.lh)> \<: <prettyprint(c.rh)>");
		}
	
		return cons;
		
	};
	
	
	
public set[Constraint[&B]] constraints_gens(term:arrayAccess(_,_), &B (AstNode) lookup_a_PlusGens, &B (AstNode) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) 
	= {};
	
public set[Constraint[&B]] constraints_gens(term:arrayCreation(_, list[AstNode] _, some(AstNode initializer)), &B (AstNode) lookup_a_PlusGens, &B (AstNode) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) 
	= { subtype(runStateTypeOf(lookup_a_PlusGens(removeParentheses(initializer)))(removeParentheses(initializer)), runStateTypeOf(lookup_a_PlusGens(term))(term)) };
	
public set[Constraint[&B]] constraints_gens(term:arrayInitializer(list[AstNode] expressions), &B (AstNode) lookup_a_PlusGens, &B (AstNode) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) 
	= { subtype(runStateTypeOf(lookup_a_PlusGens(expression))(expression), runStateTypeOf(lookup_a_PlusGens(term))(term)) | expression <- expressions };	

public set[Constraint[&B]] constraints_gens(term:assignment(AstNode lterm, nullLiteral()), &B (AstNode) lookup_a_PlusGens, &B (AstNode) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) 
	= { };

public set[Constraint[&B]] constraints_gens(term:assignment(AstNode lterm, AstNode rterm), &B (AstNode) lookup_a_PlusGens, &B (AstNode) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) 
	= { subtype(runStateTypeOf(lookup_a_PlusGens(rterm))(rterm), runStateTypeOf(lookup_a_PlusGens(lterm))(lterm)) };

public set[Constraint[&B]] constraints_gens(term:castExpression(_, AstNode e), &B (AstNode) lookup_a_PlusGens, &B (AstNode) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) 
	= { (isDownCast(term, lookup, supertypes_func)) ? subtype(runStateTypeOf(lookup_a_PlusGens(term))(term), runStateTypeOf(lookup_a_PlusGens(e))(e)) : subtype(runStateTypeOf(lookup_a_PlusGens(e))(e), runStateTypeOf(lookup_a_PlusGens(term))(term)) };

public set[Constraint[&B]] constraints_gens(term:classInstanceCreation(none(),_, [], list[AstNode] args,_), &B (AstNode) lookup_a_PlusGens, &B (AstNode) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) 
	= (!isEmpty(args)) ? { subtype(runStateTypeOf(lookup_a_PlusGens(args[i]))(args[i]), runStateTypeOf(bind(param_a_PlusGens(lookup_a_PlusGens_Open, i)(term), filter_a(bool (&V v) { return true; }, evaluation_func)))(term)) | int i <- [0..size(args) - 1], !(nullLiteral() := args[i]) } : {};
	
public set[Constraint[&B]] constraints_gens(term:classInstanceCreation(some(AstNode e),_, [], list[AstNode] args, none()), &B (AstNode) lookup_a_PlusGens, &B (AstNode) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) 
	= (!isEmpty(args)) ? { subtype(runStateTypeOf(lookup_a_PlusGens(args[i]))(args[i]), runStateTypeOf(bind(param_a_PlusGens(lookup_a_PlusGens_Open, i)(term)), filter_a(bool (&V v) { return true; }, evaluation_func))(term)) | int i <- [0..size(args) - 1], !(nullLiteral() := args[i]) } : {} 
		+ { subtype(runStateTypeOf(lookup_a_PlusGens(removeParentheses(e)))(removeParentheses(e)), runStateTypeOf(bind(decl_a_PlusGens(lookup_a_PlusGens_Open)(term), filter_a(bool (&V v) { return true; }, evaluation_func)))(term)) };
		
public set[Constraint[&B]] constraints_gens(term:classInstanceCreation(_,_, [], list[AstNode] args, some(AstNode anonym)), &B (AstNode) lookup_a_PlusGens, &B (AstNode) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) 
	= { };

public set[Constraint[&B]] constraints_gens(term:conditionalExpression(AstNode _, AstNode thenBranch, AstNode elseBranch), &B (AstNode) lookup_a_PlusGens, &B (AstNode) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) 
	= { subtype(runStateTypeOf(lookup_a_PlusGens(term))(term), runStateTypeOf(lookup_a_PlusGens(thenBranch))(thenBranch)) }
		+ { subtype(runStateTypeOf(lookup_a_PlusGens(term))(term), runStateTypeOf(lookup_a_PlusGens(elseBranch))(elseBranch)) };

public set[Constraint[&B]] constraints_gens(term:constructorInvocation(_, list[AstNode] args), &B (AstNode) lookup_a_PlusGens, &B (AstNode) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) 
	= (!isEmpty(args)) ? { subtype(runStateTypeOf(lookup_a_PlusGens(args[i]))(args[i]), runStateTypeOf(bind(param_a_PlusGens(lookup_a_PlusGens_Open, i)(term), filter_a(bool (&V v) { return true; }, evaluation_func)))(term)) | int i <- [0..size(args) - 1], !(nullLiteral() := args[i]) } : {};

public set[Constraint[&B]] constraints_gens(term:fieldAccess(AstNode e,_), &B (AstNode t) lookup_a_PlusGens, &B (AstNode t) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) 
	= { eq(runStateTypeOf(lookup_a_PlusGens(e))(e), runStateTypeOf(bind(decl_a_PlusGens(lookup_a_PlusGens_Open)(term), filter_a(bool (&V v) { return true; }, evaluation_func)))(term)) };

public set[Constraint[&B]] constraints_gens(term:methodInvocation(none(),_,_, list[AstNode] args), &B (AstNode) lookup_a_PlusGens, &B (AstNode) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) 
	= (!isEmpty(args)) ? { subtype(runStateTypeOf(lookup_a_PlusGens(args[i]))(args[i]), runStateTypeOf(bind(param_a_PlusGens(lookup_a_PlusGens_Open, i)(term), filter_a(bool (&V v) { return true; }, evaluation_func)))(term)) | int i <- [0..size(args) - 1], !(nullLiteral() := args[i]) } : {};

public set[Constraint[&B]] constraints_gens(term:methodInvocation(some(AstNode e),_,_, list[AstNode] args), &B (AstNode) lookup_a_PlusGens, &B (AstNode) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) 
	= { subtype(runStateTypeOf(lookup_a_PlusGens(removeParentheses(e)))(removeParentheses(e)), runStateTypeOf(bind(decl_a_PlusGens(lookup_a_PlusGens_Open)(term), filter_a(bool (&V v) { return true; }, evaluation_func)))(term)) }
		+ ((!isEmpty(args)) ? { subtype(runStateTypeOf(lookup_a_PlusGens(args[i]))(args[i]), runStateTypeOf(bind(param_a_PlusGens(lookup_a_PlusGens_Open, i)(term), filter_a(bool (&V v) { return true; }, evaluation_func)))(term)) | int i <- [0..size(args) - 1], !(nullLiteral() := args[i]) } : {});

public set[Constraint[&B]] constraints_gens(term:qualifiedName(_,_), &B (AstNode) lookup_a_PlusGens, &B (AstNode) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) 
	= {};

public set[Constraint[&B]] constraints_gens(term:superConstructorInvocation(some(AstNode e), _, list[AstNode] args), &B (AstNode) lookup_a_PlusGens, &B (AstNode) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) 
	= { subtype(runStateTypeOf(lookup_a_PlusGens(removeParentheses(e)))(removeParentheses(e)), runStateTypeOf(bind(decl_a_PlusGens(lookup_a_PlusGens_Open)(term), filter_a(bool (&V v) { return true; }, evaluation_func)))(term)) }
		+ (!isEmpty(args)) ? { subtype(runStateTypeOf(lookup_a_PlusGens(args[i]))(args[i]), runStateTypeOf(bind(param_a_PlusGens(lookup_a_PlusGens_Open, i)(term), filter_a(bool (&V v) { return true; }, evaluation_func)))(term)) | int i <- [0..size(args) - 1], !(nullLiteral() := args[i]) } : {};

public set[Constraint[&B]] constraints_gens(term:superFieldAccess(_,_), &B (AstNode) lookup_a_PlusGens, &B (AstNode) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) 
	= {};

public set[Constraint[&B]] constraints_gens(term:superMethodInvocation(_,_,_, list[AstNode] args), &B (AstNode) lookup_a_PlusGens, &B (AstNode) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) 
	= (!isEmpty(args)) ? { subtype(runStateTypeOf(lookup_a_PlusGens(args[i]))(args[i]), runStateTypeOf(bind(param_a_PlusGens(lookup_a_PlusGens_Open, i)(term), filter_a(bool (&V v) { return true; }, evaluation_func)))(term)) | int i <- [0..size(args) - 1], !(nullLiteral() := args[i]) } : {};

public set[Constraint[&B]] constraints_gens(term:singleVariableDeclaration(str name,_,_, some(nullLiteral()),_), &B (AstNode) lookup_a_PlusGens, &B (AstNode) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) 
	= { };

public set[Constraint[&B]] constraints_gens(term:singleVariableDeclaration(str name,_,_, some(AstNode initializer),_), &B (AstNode) lookup_a_PlusGens, &B (AstNode) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) 
	{ return { subtype(runStateTypeOf(lookup_a_PlusGens(removeParentheses(initializer)))(removeParentheses(initializer)), runStateTypeOf(lookup_a_PlusGens(setAnnotations(simpleName(name), getAnnotations(term))))(setAnnotations(simpleName(name), getAnnotations(term)))) }; }

public set[Constraint[&B]] constraints_gens(term:variableDeclarationFragment(str name, some(nullLiteral())), &B (AstNode) lookup_a_PlusGens, &B (AstNode) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) 
	= { };

public set[Constraint[&B]] constraints_gens(term:variableDeclarationFragment(str name, some(AstNode initializer)), &B (AstNode) lookup_a_PlusGens, &B (AstNode) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) 
	{ return { subtype(runStateTypeOf(lookup_a_PlusGens(removeParentheses(initializer)))(removeParentheses(initializer)), runStateTypeOf(lookup_a_PlusGens(setAnnotations(simpleName(name), getAnnotations(term))))(setAnnotations(simpleName(name), getAnnotations(term)))) }; }

public default set[Constraint[&B]] constraints_gens(AstNode term, &B (AstNode) lookup_a_PlusGens, &B (AstNode) lookup_a_PlusGens_Open, &B (&V) filter_a_2, &V (AstNode) lookup, &V (&V) evaluation_func, set[&B] (&B) supertypes_func) = {};


private bool isDownCast(term:castExpression(_, AstNode e), &V (AstNode) lookup, set[&B] (&B) supertypes_func) = (lookup(e) in supertypes_func(lookup(term))) ? true : false;

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

public set[Constraint[ParameterizedEntity]] closure(c:eq(ParameterizedEntity val1, ParameterizedEntity val2),
													set[ParameterizedEntity] (ParameterizedEntity) supertypes_func, 
												 	set[Entity] (Entity) bounds_delta, 
												 	ParameterizedEntity (Entity) toGenerics) {
	val11 = boundc(val1, bounds_delta, toGenerics);
	val22 = boundc(val2, bounds_delta, toGenerics);
	
	// println("<prettyprint(val1)> - <prettyprint(val2)>");
	// println("<prettyprint(val11)> - <prettyprint(val22)>");
	
	if(val11.genericval == zero.genericval || val22.genericval == zero.genericval) return { eq(simplify(val1), simplify(val2)) };
	 
	tparams = { tp | /tp:entity([*ids, typeParameter(_)]) <- val11.genericval } + { tp | /tp:entity([*ids, typeParameter(_)]) <- val22.genericval };
	if(isEmpty(tparams)) return { eq(simplify(val1), simplify(val2)) };
	
	assert(val11.genericval == val22.genericval);
	
	return { *closure(eq(parameterizedentity(val11.bindings, tp), parameterizedentity(val22.bindings, tp)), supertypes_func, bounds_delta, toGenerics) | tp <- tparams } + eq(simplify(val1), simplify(val2)); 
}

public set[Constraint[ParameterizedEntity]] closure(c:subtype(ParameterizedEntity val1, ParameterizedEntity val2),
													set[ParameterizedEntity] (ParameterizedEntity) supertypes_func, 
												 	set[Entity] (Entity) bounds_delta, 
												 	ParameterizedEntity (Entity) toGenerics) {
	val11 = boundc(val1, bounds_delta, toGenerics);
	val22 = boundc(val2, bounds_delta, toGenerics);
	
	// println("<prettyprint(val1)> - <prettyprint(val2)>");
    // println("<prettyprint(val11)> - <prettyprint(val22)>");
	
	if(val11.genericval == zero.genericval || val22.genericval == zero.genericval) return { subtype(simplify(val1), simplify(val2)) };
	
	if(isArrayType(val11.genericval) || isArrayType(val22.genericval)) return { subtype(simplify(val1), simplify(val2)) };
	
	tparams = { tp | /tp:entity([*ids, typeParameter(_)]) <- val11.genericval } + { tp | /tp:entity([*ids, typeParameter(_)]) <- val22.genericval };
	if(isEmpty(tparams)) return { subtype(simplify(val1), simplify(val2)) };
	
	ParameterizedEntity sup = zero;
	
	if(s <- supertypes(val11, supertypes_func, bounds_delta) + val11, s.genericval == val22.genericval) sup = s;
	
	// assert(sup != zero);
	if(sup == zero) {
		println("Assertion failed: <prettyprint(val1)> - <prettyprint(val2)>");
     	println("<prettyprint(val11)> - <prettyprint(val22)>");
		return { subtype(simplify(val1), simplify(val2)) };
	}
	
	// println("<prettyprint(sup)>");
	
	tparams = { tp | /tp:entity([*ids, typeParameter(_)]) <- sup.genericval };
	
	return { *closure(eq(parameterizedentity(sup.bindings, tp), parameterizedentity(val22.bindings, tp)), supertypes_func, bounds_delta, toGenerics) | tp <- tparams } + subtype(simplify(val1), simplify(val2)); 
}

/*
 * Not nice to duplicate code but no time !!!
 */
 
 /*
 *	Looks for a bound in case of ([.], [.]) T
 */
private ParameterizedEntity boundc(p:parameterizedentity(Bindings bs, tparam:entity([ *ids, typeParameter(str name)])), 
										   set[Entity] (Entity) bounds_delta,
										   ParameterizedEntity (Entity) toGenerics) {
	map[Entity, ParameterizedEntity] bindings_map = (!isEmpty(bs.params)) ? ( bs.params[i] : bs.args[i] | int i <- [0..size(bs.params) - 1], bs.params[i] != bs.args[i].genericval ) : ();
	ParameterizedEntity b = (bindings_map[tparam]) ? ( (!isEmpty(bounds_delta(tparam))) ? toGenerics(getOneFrom(bounds_delta(tparam))) : object);
	return boundc(parameterizedentity(concat(bs, b.bindings), b.genericval), bounds_delta, toGenerics);
}

private ParameterizedEntity boundc(parameterizedentity(Bindings bs, var:entity([ *ids, typeParameter(str name, context, ParameterizedEntity init, set[Entity] bounds) ])), 
					   set[Entity] (Entity) bounds_delta,
					   ParameterizedEntity (Entity) toGenerics) {
	ParameterizedEntity b = init ;
	if(b == zero) 
		return parameterizedentity(concat(bs, b.bindings), b.genericval);
	if(b.bindings == bindings([],[])) 
		return boundc(parameterizedentity(concat(bs, b.bindings), b.genericval), bounds_delta, toGenerics);
	list[ParameterizedEntity] args = b.bindings.args;
	list[Entity] params = b.bindings.params;
	list[ParameterizedEntity] args_parameterized 
					= (!isEmpty(args))  ?
						[ (!isTypeParameter(args[i])) 
							? parameterizedentity(entity([ typeParameter(getParamName(params[i]), 
																		 var, // nested contexts
																		 args[i], 
																		 bounds_delta(params[i])) ]) ) 
							: args[i]
						| int i <- [0..size(args) - 1] ]		
					 : [];
	// println("Nested semantics: <prettyprint(bindings(args_parameterized, params))>");
	return boundc(parameterizedentity(concat(bs, bindings(args_parameterized, params)), b.genericval), bounds_delta, toGenerics);
}

private ParameterizedEntity boundc(parameterizedentity(Bindings bs, wcard:entity([ *ids, wildcard() ])), 
										   set[Entity] (Entity) bounds_delta,
										   ParameterizedEntity (Entity) toGenerics) = parameterizedentity(bindings([], []), wcard);
private ParameterizedEntity boundc(parameterizedentity(Bindings bs, entity([ *ids, wildcard(extends(Entity b)) ])), 
										   set[Entity] (Entity) bounds_delta,
										   ParameterizedEntity (Entity) toGenerics) = toGenerics(b);
private ParameterizedEntity boundc(parameterizedentity(Bindings bs, entity([ *ids, captureof(Entity b) ])), 
										   set[Entity] (Entity) bounds_delta,
										   ParameterizedEntity (Entity) toGenerics) = boundc(parameterizedentity(bs, b), bounds_delta, toGenerics);

private default ParameterizedEntity boundc(ParameterizedEntity val, 
						_, 
						_) = val;
						
private set[ParameterizedEntity] supertypes(ParameterizedEntity v, 
							set[ParameterizedEntity] (ParameterizedEntity) supertypes_func, 
							set[Entity] (Entity) bounds_delta) {
							
	set[ParameterizedEntity] sups = supertypes_func(parameterizedentity(bindings([], []), v.genericval));
	
	set[ParameterizedEntity] sups_parameterized = {};
	
	for(sup <- sups) {
		list[ParameterizedEntity] args = sup.bindings.args;
		list[Entity] params = sup.bindings.params;
		
		list[ParameterizedEntity] args_parameterized 
					= (!isEmpty(args))  ?
						[ (!isTypeParameter(args[i])) 
							? parameterizedentity(entity([ typeParameter(getParamName(params[i]), 
																	 	entity(v.genericval.id + inherits(sup.genericval)),
																	 	args[i], 
																	 	bounds_delta(params[i])) ]) ) 
							: args[i]
					 	| int i <- [0..size(args) - 1] ]	
						: [];
		sups_parameterized += parameterizedentity(concat(v.bindings, bindings(args_parameterized, params)), sup.genericval) 
			    			  + supertypes(parameterizedentity(concat(v.bindings, bindings(args_parameterized, params)), sup.genericval), supertypes_func, bounds_delta);
	}
	return sups_parameterized + object;
}

private ParameterizedEntity simplify(parameterizedentity(Bindings bs, tparam:entity([ *ids, typeParameter(str name)]))) {
	map[Entity, ParameterizedEntity] bindings_map = (!isEmpty(bs.params)) ? ( bs.params[i] : bs.args[i] | int i <- [0..size(bs.params) - 1], bs.params[i] != bs.args[i].genericval ) : ();
	ParameterizedEntity b = simplify(parameterizedentity(concat(bs, bindings_map[tparam].bindings), bindings_map[tparam].genericval)) ? parameterizedentity(tparam);
	return b;
}

private ParameterizedEntity simplify(ParameterizedEntity val) = parameterizedentity(val.genericval);