/*
 * The module defines the basic type computations
 */
module typecomputations::TypeComputations

import List;
import Node;
import Relation;
import Set;

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;

import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;

/*
 * Imports (plugs in) the domain of type values: 
 * - their algebraic representation: &V; and 
 * - their imposed functional semantics: &V (&V) eval; &V (AstNode) lookup; set[&V] (&V) overrides; &V (&V) decl; &V (&V, int i) param;
 *
 * For example, one of the following:
 */
import typecomputations::TypeValues;
import typecomputations::TypeValuesPlusGens;

import IO;

/*
 * The type constructor of an initial monad, its inclusion and bind functions
 */
data TypeOf[&V] = typeof(&V val)
			  	  | typeid(&V val);		
public TypeOf[&V] include(&V val) = typeof(val);
public TypeOf[&V1] bind(TypeOf[&V] val, TypeOf[&V1] (&V) f)
	= top-down-break visit(val) { 
			case typeof(&V v) => f(v) 
			case typeid(&V v) => typeid(v)
		};
		
/* 
 * The type constructor of a monad modelling computations with multiple results, its inclusion and bind functions
 * '+' its run function
 */
data SetTypeOf[&V] = settypeof(set[TypeOf[&V]] vals);
public SetTypeOf[&V] includeSet(&V val) = settypeof({ include(val) });
public set[TypeOf[&V]] runSetTypeOf(settypeof(set[TypeOf[&V]] vals)) = vals;
public SetTypeOf[&V1] bind(settypeof(set[TypeOf[&V]] vals), SetTypeOf[&V1] (&V) f) 
	= settypeof({ (typeof(&V v) := val) ? *runSetTypeOf(f(v)) : val | TypeOf[&V] val <- vals });
		
/*
 * The type constructor of a monad modelling computations with a state passed around, its inclusion and bind functions
 * '+' its run function
 */  
data StateTypeOf[&V] = statetypeof(SetTypeOf[&V] (AstNode) val);
public StateTypeOf[&V] includeState(&V val) = statetypeof(SetTypeOf[&V] (AstNode t) { return includeSet(val); });
public SetTypeOf[&V] (AstNode) runStateTypeOf(statetypeof(SetTypeOf[&V] (AstNode) val)) = val;
public StateTypeOf[&V] bind(statetypeof(SetTypeOf[&V] (AstNode) sval), StateTypeOf[&V1] (&V) f)
	= statetypeof( SetTypeOf[&V1] (AstNode t) { 
		return settypeof( { v | /TypeOf[&V] v <- { (typeof(&V val) := tval) ? runSetTypeOf(runStateTypeOf(f(val))(t)) : { tval } | TypeOf[&V] tval <- runSetTypeOf(sval(t)) } }); } );

@doc{ Lifting to computations }
public TypeOf[&V] (AstNode) lift(&V (AstNode) f)
	= TypeOf[&V] (AstNode t) { return !isType(f(v)) ? include(f(v)) : typeid(f(v)); };
	
/*
 * Evaluation
 */
public &V1 (TypeOf[&V]) lift(&V1 (&V) f)
	= &V1 (TypeOf[&V] val) { 
			return visit(val) { 
					case typeof(&V v) => f(v)
					case typeid(&V v) => v 
			}; 
	  };

@doc{ Lifting to stateful computations }
public SetTypeOf[&V] (AstNode) lift(TypeOf[&V] (AstNode) f) 
	= SetTypeOf[&V] (AstNode t) { return settypeof( { f(t) } ); };
	
public SetTypeOf[&V1] (&V) lift(TypeOf[&V1] (&V) f) 
	= SetTypeOf[&V1] (&V val) { return settypeof( { f(val) } ); };

/*
 * Evaluation
 */	
public set[&V1] (SetTypeOf[&V]) lift(&V1 (TypeOf[&V]) f) = set[&V1] (SetTypeOf[&V] val) { return { f(v) | TypeOf[&V] v <- runSetTypeOf(val) }; };

public StateTypeOf[&V1] (AstNode) lift(SetTypeOf[&V1] (AstNode) f) 
	= StateTypeOf[&V1] (AstNode t) { return statetypeof( SetTypeOf[&V1] (AstNode tt) { return f(t); } ); }; 
	
public StateTypeOf[&V1] (&V) lift(SetTypeOf[&V1] (&V) f) 
	= StateTypeOf[&V1] (&V val) { return statetypeof( (AstNode t) { return f(val); } ); }; 

/*
 * Evaluation
 */
public set[&V1] (AstNode) (StateTypeOf[&V]) lift(set[&V1] (SetTypeOf[&V]) f) = set[&V1] (AstNode) (StateTypeOf[&V] val) { return set[&V1] (AstNode t) { return f(runStateTypeOf(val)(t)); }; };


/*
 * Ordinary composition operator
 */
public &V1 o(&V val, &V1 (&V) f) = f(val); 



/* 
 * Type computations :
 */
@doc{ Type computation that produces the type computation constants }
public TypeOf[&V] cconst(&V val) = typeid(eval(val));
	
@doc{ The evaluation function lifted to type computations }
public &V ceval(TypeOf[&V] val) = bind(val, cconst).val;
		
@doc{ Basic lookup computation }
public TypeOf[&V] clookup(AstNode t) = include(lookup(t));

@doc{ Override computation }
public SetTypeOf[&V] coverrides(&V val) = includeSet( { include(override) | override <- overrides(val) } );
	
@doc{ Decl computation }
public TypeOf[&V] cdecl(&V val) = include(decl(val));

@doc{ Param computation }
public TypeOf[&V] cparam(&V val, int i) = include(param(val, i));

// ----- Bunch of prettyprint utility functions -------------------------------------
public str prettyprint(set[&V] vals) = "{ <for(val<-vals){><prettyprint(val)><}> }";
public str prettyprint(typeof(&V val)) = "[<prettyprint(val)>]";
public str prettyprint(typeid(&V val)) = "[<prettyprint(val)>]";
public str prettyprint(settypeof(set[TypeOf[&V]] vals)) = "{ <for(val<-vals){><prettyprint(val)>;<}> }";
public str prettyprint(none()) = "_";
public str prettyprint(some(&V val)) = "<prettyprint(val)>";