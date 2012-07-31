module typecomputations::TypeComputationsPlusGens

import List;
import Node;
import Relation;
import Set;

import lang::java::jdt::Java;

import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::JavaADT;

import typecomputationbasedframework4refactorings::TypeValues;
import typecomputationbasedframework4refactorings::TypeValuesPlusGens;
import typecomputationbasedframework4refactorings::TypeComputations;

import IO;

/*
 * Type computation plus generics
 */

public  set[&V] (AstNode) (set[&V] (AstNode)) eval_a_PlusGens(&V (AstNode, &V) parameterize) =
	set[&V] (AstNode) (set[&V] (AstNode) val) { 
		return set[&V] (AstNode t) { 
			return { parameterize(t, v) | v <- val(t) };
		}; 
	};
	
public StateTypeOf[&V] (AstNode) lookup_a_PlusGens(&V (AstNode) lookup, 
												   &V (&V) eval, 
												   &V (&V) parameterize_eval, 
												   &V (AstNode, AstNode, &V, &V) parameterize_lookup,
												   &V (AstNode, &V) parameterize_lookup_reduced,
												   StateTypeOf[&V] (&V) filter_a_1,
												   StateTypeOf[&V] (&V) filter_a_2) 
	= StateTypeOf[&V] (AstNode t) {  
		return (some(subt) := subterm(t)) ? 
					bind( bind( bind( lift(lift(lookup_a(lookup)))(t), 
									  filter_a_1), 
							  	StateTypeOf[&V] (&V val) {
									return statetypeof(SetTypeOf[&V] (AstNode t) { 
										return settypeof({ typeof( o ( o (lookup_a_PlusGens(lookup, 
																							eval, 
																							parameterize_eval, 
																							parameterize_lookup, 
																							parameterize_lookup_reduced, 
																							filter_a_1, 
																						    filter_a_2)(subt), 
														 				  lift(lift(eval_a(parameterize_eval)))), 
																   		&V (set[&V] (AstNode) val_T) { 
																   				return parameterize_lookup(t, subt, val, getOneFrom(val_T(subt))); } ) ) }); }) ;
								}), 
							filter_a_2) 
					: bind(	bind( bind( lift(lift(lookup_a(lookup)))(t), 
										filter_a_1),
								  StateTypeOf[&V] (&V val) {
										return statetypeof(SetTypeOf[&V] (AstNode t) { 
											return settypeof({ include(parameterize_lookup_reduced(t, val)) }); });
								 }), 
							filter_a_2); };
 
private AstNode this(Entity scope) = thisExpression(none())[@bindings = ("typeBinding" : scope)]; 
@doc{A function that returns a subterm which is sub-looked up}
public Option[AstNode] subterm(e:classInstanceCreation(none(),_,[],_,none())) = none();
public Option[AstNode] subterm(e:classInstanceCreation(some(AstNode expr),_,[],_,none())) = some(removeParentheses(expr));
public Option[AstNode] subterm(e:classInstanceCreation(_,_,[],_,some(AstNode anonymClass))) = none(); 
public Option[AstNode] subterm(e:fieldAccess(AstNode expr,_)) = some(removeParentheses(expr)); 
public Option[AstNode] subterm(e:methodInvocation(none(),_,_,_)) = some(this(e@scope));
public Option[AstNode] subterm(e:methodInvocation(some(AstNode expr),_,_,_)) = some(removeParentheses(expr));
public Option[AstNode] subterm(e:qualifiedName(AstNode qname,_)) = (isVariableBinding(lookup(e))) ? some(qname) : none(); 
public Option[AstNode] subterm(e:simpleName(_)) = (isFieldBinding(lookup(e)) && !isArrayType(getType(e))) ? some(this(e@scope)) : none();
public Option[AstNode] subterm(e:superConstructorInvocation(none(),_,_)) = some(this(e@scope));
public Option[AstNode] subterm(e:superConstructorInvocation(some(AstNode expr),_,_)) = some(removeParentheses(expr));
public Option[AstNode] subterm(e:superFieldAccess(none(),_)) = some(this(e@scope));
public Option[AstNode] subterm(e:superFieldAccess(some(AstNode qualifier),_)) = some(qualifier); 
public Option[AstNode] subterm(e:superMethodInvocation(none(),_,_,_)) = some(this(e@scope));
public Option[AstNode] subterm(e:superMethodInvocation(some(AstNode qualifier),_,_,_)) = some(qualifier); 
public default Option[AstNode] subterm(AstNode t) = none();

public AstNode removeParentheses(term:parenthesizedExpression(AstNode expression)) = removeParentheses(expression);
public AstNode removeParentheses(AstNode expression) = expression;

public StateTypeOf[&V] (&V) filter_a(bool (&V) p, &V (&V) eval) 
	= StateTypeOf[&V] (&V val) { 
		return statetypeof( SetTypeOf[&V] (AstNode t) { 
			return settypeof({ (p(val)) ? typeid(eval(val)) : include(val) }); } ); 
	  };

public StateTypeOf[&V] (AstNode) lookup_a_PlusGens_Open(&V (AstNode) lookup, 
												   &V (&V) eval, 
												   &V (&V) parameterize_eval, 
												   &V (AstNode, AstNode, &V, &V) parameterize_lookup,
												   &V (AstNode, &V) parameterize_lookup_reduced,
												   StateTypeOf[&V] (&V) filter_a_1,
												   StateTypeOf[&V] (&V) filter_a_2) 
	= StateTypeOf[&V] (AstNode t) {  
		return (some(subt) := subterm(t)) ?  
					bind( lift(lift(lookup_a(lookup)))(t), 
							   StateTypeOf[&V] (&V val) {
									return statetypeof(SetTypeOf[&V] (AstNode t) { 
										return settypeof({ typeof( o ( o (lookup_a_PlusGens(lookup, 
																							eval, 
																							parameterize_eval, 
																							parameterize_lookup, 
																							parameterize_lookup_reduced, 
																							filter_a_1, 
																							filter_a_2)(subt), 
																 		   lift(lift(eval_a(parameterize_eval)))), 
																	   &V (set[&V] (AstNode) val_T) { 
																		 	return parameterize_lookup(t, subt, val, getOneFrom(val_T(subt))); } ) ) }); }) ;
						}) 
					: bind(lift(lift(lookup_a(lookup)))(t), 
						   StateTypeOf[&V] (&V val) {
								return statetypeof(SetTypeOf[&V] (AstNode t) { 
										return settypeof({ include(parameterize_lookup_reduced(t, val)) }); });
						   }); 
	 };
	 
public StateTypeOf[ParameterizedEntity] (ParameterizedEntity val) paramc(int i) 
	= StateTypeOf[ParameterizedEntity] (ParameterizedEntity val) {
		return includeState(paramc(val, i));
	};
	
public StateTypeOf[ParameterizedEntity] (ParameterizedEntity val) declc() 
	= StateTypeOf[ParameterizedEntity] (ParameterizedEntity val) {
		return includeState(declc(val));
	};
	
public StateTypeOf[&V] (AstNode t) param_a_PlusGens(StateTypeOf[&V] (AstNode t) lookup_a_PlusGens_Open, int i) 
	= StateTypeOf[&V] (AstNode t) {
		return bind(lookup_a_PlusGens_Open(t), paramc(i));
	};
	
public StateTypeOf[&V] (AstNode t) decl_a_PlusGens(StateTypeOf[&V] (AstNode t) lookup_a_PlusGens_Open) 
	= StateTypeOf[&V] (AstNode t) {
		return bind(lookup_a_PlusGens_Open(t), declc());
	};
											
