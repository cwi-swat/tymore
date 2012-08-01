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
// lookup := lift(lift(lift1(lookup(facts.mapper))))	
// eval := lift(lift(lift2(evalPlusGens(facts))))
public StateTypeOf[&V] (AstNode) lookupPlusGens(StateTypeOf[&V] (&V) lookup, set[&V] (AstNode) (StateTypeOf[&V]) eval, StateTypeOf[&V] (&V) filter1, StateTypeOf[&V] (&V) filter2, CompilUnitGens facts) 
	= StateTypeOf[&V] (AstNode t) {  
		return (some(subt) := subterm(t)) ? 
					bind( bind( bind( lookup(t), filter1), 
							  	StateTypeOf[&V] (&V val) {
									return statetypeof(SetTypeOf[&V] (AstNode t) { 
										return settypeof({ typeof(v) | v <- o ( o (lookupPlusGens(lookup, eval, filter1, filter2, facts)(subt), eval), 
																   	  			set[&V] (set[&V] (AstNode) vals_T) { 
																   						return { parameterize2(facts)(t, subt, val, val_T) | &V val_T <- vals_T(subt) }; 
																   					} 
																   			   )
														  }); });
								}), 
						  filter2) 
				  : bind( bind( bind( lookup(t), filter1),
								StateTypeOf[&V] (&V val) {
									return statetypeof(SetTypeOf[&V] (AstNode t) { 
										return settypeof({ include(parameterize2Reduced(facts)(t, val)) }); });
								 }), 
						  filter2); };
						  
public StateTypeOf[&V] (AstNode) lookupPlusGensOpen(StateTypeOf[&V] (&V) lookup, set[&V] (AstNode) (StateTypeOf[&V]) eval, StateTypeOf[&V] (&V) filter1, StateTypeOf[&V] (&V) filter2, CompilUnitGens facts) 
	= StateTypeOf[&V] (AstNode t) {  
		return (some(subt) := subterm(t)) ?  
					bind( lookup(t), 
							   StateTypeOf[&V] (&V val) {
									return statetypeof(SetTypeOf[&V] (AstNode t) { 
										return settypeof({ typeof(v) | v <- o ( o (lookupPlusGens(lookup, eval, filter1, filter2, facts)(subt), eval), 
																	   			set[&V] (set[&V] (AstNode) vals_T) { 
																		 					return { parameterize2(facts)(t, subt, val, val_T(subt)) | &V val_T <- vals_T(subt)}; } ) 
														 }); }) ;
						       }) 
				  : bind(lookup(t), 
						 StateTypeOf[&V] (&V val) {
								return statetypeof(SetTypeOf[&V] (AstNode t) { 
										return settypeof({ include(parameterize2Reduced(facts)(t, val)) }); });
						   }); 
	 };
 
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

public AstNode removeParentheses(parenthesizedExpression(AstNode expression)) = removeParentheses(expression);
public AstNode removeParentheses(AstNode expression) = expression;

public StateTypeOf[&V] (&V) filter(bool (&V) p, &V (&V) eval) 
	= StateTypeOf[&V] (&V val) { 
		return statetypeof( SetTypeOf[&V] (AstNode t) { 
			return settypeof({ (p(val)) ? typeid(eval(val)) : include(val) }); } ); 
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
											
