@doc{The module defines the domain of type values:
  - their algebraic representation: Entity; and
  - their functional semantics: Entity (Entity) eval; 
  								Entity (AstNode) lookup; 
  								set[Entity] (Entity) overrides; 
  								Entity (Entity) decl; (unique representation of the declaring type of a declaration) 
  								Entity (Entity, int i) param; (unique representation of the declaring type of a declaration parameter)}
module typecomputations::TypeValues

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;
import lang::java::jdt::refactorings::PrettyPrintUtil;
import lang::java::jdt::refactorings::ValuesUtil;

import IO;
import List;
import Set;

@doc{Evaluation function: evaluates a declaration type value to the associated declared type}	
public Entity eval(entity([ *ids, constr(_) ])) = entity(ids);		
public Entity eval(entity([ *ids, constr(_,_) ])) = entity(ids);
public Entity eval(entity([ *_, method(_,_, Entity declaredType) ])) = declaredType;
public Entity eval(entity([ *_, method(_,_,_, Entity declaredType) ])) = declaredType;
public Entity eval(entity([ *_, enumConstant(_, Entity declaredType) ])) = declaredType;
public Entity eval(entity([ *_, field(_, Entity declaredType) ])) = declaredType;
public Entity eval(entity([ *_, \parameter(_, Entity declaredType) ])) = declaredType;
public Entity eval(entity([ *_, variable(_, Entity declaredType, _) ])) = declaredType;
public Entity eval(entity([ *_, anonymous(_, Entity declaredType) ])) = declaredType;
public Entity eval(entity([ *_, inherits(Entity declaredType) ])) = declaredType;
/* Note: 
* 	in case of constructors, i.e. new A().new B(), the declaring type is evaluated to the type that declares the type, 
*   objects of which the constructor creates */ 
public Entity eval(entity([ *ids, constr(_), decl() ])) = eval(entity(ids + decl()));
public Entity eval(entity([ *ids, constr(_,_), decl() ])) = eval(entity(ids + decl()));
public Entity eval(entity([ *ids, id, decl() ])) = entity(ids);
public Entity eval(entity([ *_, constr(list[Entity] params), \parameter(int i) ])) = params[i];
public Entity eval(entity([ *_, method(_, list[Entity] params, _), \parameter(int i) ])) = params[i];
public Entity eval(entity([ *_, constr(_, list[Entity] params), \parameter(int i) ])) = params[i];
public Entity eval(entity([ *_, method(_,_, list[Entity] params,_), \parameter(int i) ])) = params[i];
public default Entity eval(Entity val) = val;

@doc{Basic lookup semantics, the typed terms are: expressions (e) and declarations (d)}
public Entity lookup(e:arrayAccess(_,_)) = getType(e);
public Entity lookup(e:arrayCreation(_,_,_)) = getType(e);
public Entity lookup(e:arrayInitializer(_)) = getType(e);
public Entity lookup(e:assignment(AstNode le,_)) = lookup(le);
public Entity lookup(e:booleanLiteral(_)) = getType(e);
public Entity lookup(e:castExpression(_,_)) = entity([anonymous(e@location, getType(e))]);
public Entity lookup(e:characterLiteral(_)) = getType(e);
public Entity lookup(e:classInstanceCreation(_,_,_,_,_)) = e@bindings["methodBinding"];
public Entity lookup(e:conditionalExpression(_,_,_)) = getType(e); 
public Entity lookup(s:constructorInvocation(_,_)) = s@bindings["methodBinding"];
public Entity lookup(e:fieldAccess(_,_)) = e@bindings["variableBinding"]; 
public Entity lookup(e:infixExpression(_,_,_,_)) = getType(e);
public Entity lookup(e:instanceofExpression(_,_)) = getType(e);
public Entity lookup(e:markerAnnotation(_)) = getType(e);
public Entity lookup(e:methodInvocation(_,_,_,_)) = e@bindings["methodBinding"]; 
public Entity lookup(e:normalAnnotation(_,_)) = getType(e);
public Entity lookup(e:nullLiteral()) = getType(e);
public Entity lookup(e:numberLiteral(_)) = getType(e);
public Entity lookup(e:parenthesizedExpression(_)) = getType(e);
public Entity lookup(e:postfixExpression(_,_)) = getType(e);
public Entity lookup(e:prefixExpression(_,_)) = getType(e);
public Entity lookup(e:qualifiedName(qualifier,_)) = ("variableBinding" in e@bindings && !isArrayType(getType(qualifier))) ? e@bindings["variableBinding"] : getType(e);  
public Entity lookup(e:simpleName(_)) = ("variableBinding" in e@bindings && !isArrayType(getType(e))) ? e@bindings["variableBinding"] : getType(e); 
public Entity lookup(e:singleMemberAnnotation(_,_)) = getType(e);
public Entity lookup(e:stringLiteral(_)) = getType(e);
public Entity lookup(s:superConstructorInvocation(_,_,_)) = s@bindings["methodBinding"]; 
public Entity lookup(e:superFieldAccess(_,_)) = e@bindings["variableBinding"]; 
public Entity lookup(e:superMethodInvocation(_,_,_,_)) = e@bindings["methodBinding"]; 
public Entity lookup(e:thisExpression(_)) = getType(e); 
public Entity lookup(e:typeLiteral(_)) = getType(e); 
public Entity lookup(e:variableDeclarationExpression(_,_,_)) = getType(e); 
public Entity lookup(d:anonymousClassDeclaration(_)) = getType(d);
public Entity lookup(d:typeDeclaration(_,_,_,_,_,_,_)) = getType(d);
public Entity lookup(d:methodDeclaration(_,_,_,_,_,_,_)) = getType(d);
public Entity lookup(d:singleVariableDeclaration(_,_,_,_,_)) = d@bindings["variableBinding"];
public Entity lookup(d:variableDeclarationFragment(_,_)) = d@bindings["variableBinding"];
public default Entity lookup(AstNode t) { println("The term <t> does not have the lookup semantics!"); return zero(); }

@doc{Basic typing semantics}
public Entity getType(AstNode t) = t@bindings["typeBinding"];

@doc{Overrides semantics}
public set[Entity] overrides(CompilUnit facts, Entity val) = facts["overrides_func"][val];

public Entity inherits(Entity t1, Entity t2) = entity(t1.id + inherits(t2));
