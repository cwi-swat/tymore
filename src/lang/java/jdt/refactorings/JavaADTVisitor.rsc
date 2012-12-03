module lang::java::jdt::refactorings::JavaADTVisitor

import lang::java::jdt::Java;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::JavaADT;

import IO;

public AstNode visitADT(compilationUnit(Option[AstNode] package, list[AstNode] imports, list[AstNode] typeDeclarations))
	= compilationUnit(some(AstNode p) := package ? some(visitADT(p)) : none(), [ visitADT(i) | AstNode i <- imports ], [ visitADT(td) | AstNode td <- typeDeclarations ]);
public AstNode visitADT(anonymousClassDeclaration(list[AstNode] bodyDeclarations)) = anonymousClassDeclaration([ visitADT(n)| AstNode n <- bodyDeclarations ]);
public AstNode visitADT(annotationTypeDeclaration(list[Modifier] modifiers, list[AstNode] annotations, str name, list[AstNode] bodyDeclarations)) 
	= annotationTypeDeclaration(modifiers, [ visitADT(a) | AstNode a <- annotations ], name, [ visitADT(b) | AstNode b <- bodyDeclarations ]);
public AstNode visitADT(annotationTypeMemberDeclaration(list[Modifier] modifiers, list[AstNode] annotations, AstNode typeArgument, str name, Option[AstNode] defaultBlock)) 
	= annotationTypeMemberDeclaration(modifiers, [ visitADT(a) | AstNode a <- annotations ], visitADT(typeArgument), name, some(AstNode db) := defaultBlock ? some(visitADT(db)): none());
public AstNode visitADT(enumDeclaration(list[Modifier] modifiers, list[AstNode] annotations, str name, list[AstNode] implements, list[AstNode] enumConstants, list[AstNode] bodyDeclarations)) 
	= enumDeclaration(modifiers, [ visitADT(a) | AstNode a <- annotations ], name, [ visitADT(i) | AstNode i <- implements ], [ visitADT(e) | AstNode e <- enumConstants ], [ visitADT(b) | AstNode b <- bodyDeclarations ]);
public AstNode visitADT(enumConstantDeclaration(list[Modifier] modifiers, list[AstNode] annotations, str name, list[AstNode] arguments, Option[AstNode] anonymousClassDeclaration))
	= enumConstantDeclaration(modifiers, [ visitADT(a) | AstNode a <- annotations ], name, [ visitADT(a) | AstNode a <- arguments ], some(AstNode ac) := anonymousClassDeclaration ? some(visitADT(ac)) : none() );
public AstNode visitADT(typeDeclaration(list[Modifier] modifiers, list[AstNode] annotations, str objectType, str name, list[AstNode] genericTypes, Option[AstNode] extends, list[AstNode] implements, list[AstNode] bodyDeclarations))
	= typeDeclaration(modifiers, [ visitADT(a) | AstNode a <- annotations ], objectType, name, [ visitADT(gt) | AstNode gt <- genericTypes ], some(AstNode ext) := extends ? some(visitADT(ext)) : none(), [ visitADT(i) | AstNode i <- implements ], [ visitADT(bd) | AstNode bd <- bodyDeclarations ]);
public AstNode visitADT(fieldDeclaration(list[Modifier] modifiers, list[AstNode] annotations, AstNode \type, list[AstNode] fragments))
	= fieldDeclaration(modifiers, [ visitADT(a) | AstNode a <- annotations ], visitADT(\type), [ visitADT(f) | AstNode f <- fragments ]);
public AstNode visitADT(AstNode::initializer(list[Modifier] modifiers, list[AstNode] annotations, AstNode body))
	= AstNode::initializer(modifiers, [ visitADT(a) | AstNode a <- annotations ], visitADT(body));
public AstNode visitADT(methodDeclaration(list[Modifier] modifiers, list[AstNode] annotations, list[AstNode] genericTypes, Option[AstNode] returnType, str name, list[AstNode] parameters, list[AstNode] possibleExceptions, Option[AstNode] implementation))
	= methodDeclaration(modifiers, [ visitADT(a) | AstNode a <- annotations ], [ visitADT(gt) | AstNode gt <- genericTypes ], some(AstNode rt) := returnType ? some(visitADT(rt)) : none(), name, [ visitADT(p) | AstNode p <- parameters ], [ visitADT(pe) | AstNode pe <- possibleExceptions ], some(AstNode i) := implementation ? some(visitADT(i)) : none() );
public AstNode visitADT(importDeclaration(str name, bool staticImport, bool onDemand))
	= importDeclaration(name, staticImport, onDemand);
public AstNode visitADT(packageDeclaration(str name, list[AstNode] annotations))
	= packageDeclaration(name, [ visitADT(a) | AstNode a <- annotations ]);
public AstNode visitADT(singleVariableDeclaration(str name, list[Modifier] modifiers, list[AstNode] annotations, AstNode \type, Option[AstNode] initializer, bool isVarargs))
	= singleVariableDeclaration(name, modifiers, [ visitADT(a) | AstNode a <- annotations ], visitADT(\type), some(AstNode i) := initializer ? some(visitADT(i)) : none(), isVarargs );
public AstNode visitADT(variableDeclarationFragment(str name, Option[AstNode] initializer))
	= variableDeclarationFragment(name, some(AstNode i) := initializer ? some(visitADT(i)) : none());
public AstNode visitADT(AstNode::typeParameter(str name, list[AstNode] extendsList))
	= AstNode::typeParameter(name, [ visitADT(ext) | AstNode ext <-  extendsList ]);

// Expressions
public AstNode visitADT(markerAnnotation(str typeName)) = markerAnnotation(typeName);
public AstNode visitADT(normalAnnotation(str typeName, list[AstNode] memberValuePairs)) = normalAnnotation(typeName, [ visitADT(mvp) | AstNode mvp <- memberValuePairs ]);
public AstNode visitADT(memberValuePair(str name, AstNode \value)) = memberValuePair(name, visitADT(\value));				
public AstNode visitADT(singleMemberAnnotation(str typeName, AstNode \value)) = singleMemberAnnotation(typeName, visitADT(\value));
public AstNode visitADT(arrayAccess(AstNode array, AstNode index)) = arrayAccess(visitADT(array), visitADT(index));
public AstNode visitADT(arrayCreation(AstNode \type, list[AstNode] dimensions, Option[AstNode] initializer)) 
	= arrayCreation(visitADT(\type), [ visitADT(d) | AstNode d <- dimensions ], some(AstNode i) := initializer ? some(visitADT(i)) : none());
public AstNode visitADT(arrayInitializer(list[AstNode] expressions)) = arrayInitializer([ visitADT(e) | AstNode e <- expressions ]);
public AstNode visitADT(assignment(AstNode leftSide, AstNode rightSide)) = assignment(visitADT(leftSide), visitADT(rightSide));
public AstNode visitADT(booleanLiteral(bool boolValue)) = booleanLiteral(boolValue);
public AstNode visitADT(castExpression(AstNode \type, AstNode expression)) = castExpression(visitADT(\type), visitADT(expression));
public AstNode visitADT(characterLiteral(str charValue)) = characterLiteral(charValue);
public AstNode visitADT(classInstanceCreation(Option[AstNode] optionalExpression, AstNode \type, list[AstNode] genericTypes, list[AstNode] typedArguments, Option[AstNode] anonymousClassDeclaration))
	= classInstanceCreation(some(AstNode oe) := optionalExpression ? some(visitADT(oe)) : none(), visitADT(\type), [ visitADT(gt) | AstNode gt <- genericTypes ], [ visitADT(ta) | AstNode ta <- typedArguments ], some(AstNode ac) := anonymousClassDeclaration ? some(visitADT(ac)) : none());
public AstNode visitADT(conditionalExpression(AstNode expression, AstNode thenBranch, AstNode elseBranch)) = conditionalExpression(visitADT(expression), visitADT(thenBranch), visitADT(elseBranch));
public AstNode visitADT(fieldAccess(AstNode expression, str name)) = fieldAccess(visitADT(expression), name);
public AstNode visitADT(infixExpression(str operator, AstNode leftSide, AstNode rightSide, list[AstNode] extendedOperands)) = infixExpression(operator, visitADT(leftSide), visitADT(rightSide), [ visitADT(eo) | AstNode eo <- extendedOperands ]);
public AstNode visitADT(instanceofExpression(AstNode leftSide, AstNode rightSide)) = instanceofExpression(visitADT(leftSide), visitADT(rightSide));
public AstNode visitADT(methodInvocation(Option[AstNode] optionalExpression, list[AstNode] genericTypes, str name, list[AstNode] typedArguments)) 
	= methodInvocation(some(AstNode oe) := optionalExpression ? some(visitADT(oe)) : none(), [ visitADT(gt) | AstNode gt <- genericTypes ], name, [ visitADT(ta) | AstNode ta <- typedArguments ]);
public AstNode visitADT(superMethodInvocation(Option[AstNode] optionalQualifier, list[AstNode] genericTypes, str name, list[AstNode] typedArguments))
	= superMethodInvocation(some(AstNode oq) := optionalQualifier ? some(visitADT(oq)) : none(), [ visitADT(gt) | AstNode gt <- genericTypes ], name, [ visitADT(ta) | AstNode ta <- typedArguments ] );
public AstNode visitADT(qualifiedName(AstNode qualifier, str name)) = qualifiedName(visitADT(qualifier), name);
public AstNode visitADT(simpleName(str name)) = simpleName(name);
public AstNode visitADT(nullLiteral()) = nullLiteral();
public AstNode visitADT(numberLiteral(str number)) = numberLiteral(number);
public AstNode visitADT(parenthesizedExpression(AstNode expression)) = parenthesizedExpression(visitADT(expression));
public AstNode visitADT(postfixExpression(AstNode operand, str operator)) = postfixExpression(visitADT(operand), operator);
public AstNode visitADT(prefixExpression(AstNode operand, str operator)) = prefixExpression(visitADT(operand), operator);
public AstNode visitADT(stringLiteral(str stringValue)) = stringLiteral(stringValue);
public AstNode visitADT(superFieldAccess(Option[AstNode] optionalQualifier, str name)) = superFieldAccess(some(AstNode oq) := optionalQualifier ? some(visitADT(oq)) : none(), name);
public AstNode visitADT(thisExpression(Option[AstNode] optionalQualifier)) = thisExpression(some(AstNode oq) := optionalQualifier ? some(visitADT(oq)) : none());
public AstNode visitADT(typeLiteral(AstNode \type)) = typeLiteral(visitADT(\type));
public AstNode visitADT(variableDeclarationExpression(list[Modifier] modifiers, list[AstNode] annotations, AstNode \type, list[AstNode] fragments)) = variableDeclarationExpression(modifiers, [ visitADT(a) | AstNode a <- annotations ], visitADT(\type), [ visitADT(f) | AstNode f <- fragments ]);						

// Statements
public AstNode visitADT(assertStatement(AstNode expression, Option[AstNode] message)) = assertStatement(visitADT(expression), some(AstNode m) := message ? some(visitADT(m)) : none());
public AstNode visitADT(block(list[AstNode] statements)) = block([ visitADT(s) | AstNode s <- statements ]);
public AstNode visitADT(breakStatement(Option[str] label)) = breakStatement(label);
public AstNode visitADT(constructorInvocation(list[AstNode] genericTypes, list[AstNode] typedArguments))
	= constructorInvocation([ visitADT(gt) | AstNode gt <- genericTypes ], [ visitADT(ta) | AstNode ta <- typedArguments ]);
public AstNode visitADT(superConstructorInvocation(Option[AstNode] optionalExpression, list[AstNode] genericTypes, list[AstNode] typedArguments))
	= superConstructorInvocation(some(AstNode oe) := optionalExpression ? some(visitADT(oe)) : none(), [ visitADT(gt) | AstNode gt <- genericTypes ], [ visitADT(ta) | AstNode ta <- typedArguments ]);
public AstNode visitADT(continueStatement(Option[str] label)) = continueStatement(label);
public AstNode visitADT(doStatement(AstNode body, AstNode whileExpression)) = doStatement(visitADT(body), visitADT(whileExpression));
public AstNode visitADT(emptyStatement()) = emptyStatement();
public AstNode visitADT(enhancedForStatement(AstNode parameter, AstNode collectionExpression, AstNode body))
	= enhancedForStatement(visitADT(parameter), visitADT(collectionExpression), visitADT(body));
public AstNode visitADT(expressionStatement(AstNode expression)) = expressionStatement(visitADT(expression));
public AstNode visitADT(forStatement(list[AstNode] initializers, Option[AstNode] optionalBooleanExpression, list[AstNode] updaters, AstNode body))
	= forStatement([ visitADT(i) | AstNode i <- initializers ], some(AstNode obe) := optionalBooleanExpression ? some(visitADT(obe)) : none(), [ visitADT(u) | AstNode u <- updaters ], visitADT(body));
public AstNode visitADT(ifStatement(AstNode booleanExpression, AstNode thenStatement, Option[AstNode] elseStatement))
	= ifStatement(visitADT(booleanExpression), visitADT(thenStatement), some(AstNode es) := elseStatement ? some(visitADT(es)) : none());
public AstNode visitADT(labeledStatement(str name, AstNode body))
	= labeledStatement(name, visitADT(body));
public AstNode visitADT(returnStatement(Option[AstNode] optionalExpression)) = returnStatement(some(AstNode oe) := optionalExpression ? some(visitADT(oe)) : none());
public AstNode visitADT(switchStatement(AstNode expression, list[AstNode] statements)) = switchStatement(visitADT(expression), [ visitADT(s) | AstNode s <- statements ]);
public AstNode visitADT(switchCase(bool isDefault, Option[AstNode] optionalExpression)) = switchCase(isDefault, some(AstNode oe) := optionalExpression ? some(visitADT(oe)) : none());
public AstNode visitADT(synchronizedStatement(AstNode expression, AstNode body)) = synchronizedStatement(visitADT(expression), visitADT(body));
public AstNode visitADT(throwStatement(AstNode expression)) = throwStatement(visitADT(expression));
public AstNode visitADT(tryStatement(AstNode body, list[AstNode] catchClauses, Option[AstNode] \finally))
	= tryStatement(visitADT(body), [ visitADT(cc) | AstNode cc <- catchClauses ], some(AstNode f) := \finally ? some(visitADT(f)) : none());										
public AstNode visitADT(catchClause(AstNode exception, AstNode body)) = catchClause(visitADT(exception), visitADT(body));
public AstNode visitADT(typeDeclarationStatement(AstNode typeDeclaration)) = typeDeclarationStatement(visitADT(typeDeclaration));
public AstNode visitADT(variableDeclarationStatement(list[Modifier] modifiers, list[AstNode] annotations, AstNode \type, list[AstNode] fragments))
	= variableDeclarationStatement(modifiers, [ visitADT(a) | AstNode a <- annotations ], visitADT(\type), [ visitADT(f) | AstNode f <- fragments ]);
public AstNode visitADT(whileStatement(AstNode expression, AstNode body)) = whileStatement(visitADT(expression), visitADT(body));
							
// Types
public AstNode visitADT(arrayType(AstNode \typeOfArray)) = arrayType(visitADT(\typeOfArray));
public AstNode visitADT(parameterizedType(AstNode \typeOfParam, list[AstNode] genericTypes)) = parameterizedType(visitADT(\typeOfParam), [ visitADT(gt) | AstNode gt <- genericTypes ]);
public AstNode visitADT(qualifiedType(AstNode qualifier, str name)) = qualifiedType(visitADT(qualifier), name);
public AstNode visitADT(primitiveType(PrimitiveType primitive)) = primitiveType(primitive);
public AstNode visitADT(simpleType(str name)) = simpleType(name);
public AstNode visitADT(unionType(list[AstNode] types)) = unionType([ visitADT(t) | AstNode t <- types ]);
public AstNode visitADT(wildcardType(Option[AstNode] bound, Option[str] lowerOrUpper))
	= wildcardType(some(AstNode b) := bound ? some(visitADT(b)) : none(), lowerOrUpper);
																			
// Comments 
public AstNode visitADT(blockComment()) = blockComment();
public AstNode visitADT(lineComment()) = lineComment();

// Javadoc
public AstNode visitADT(javadoc()) = javadoc();
public AstNode visitADT(tagElement()) = tagElement();
public AstNode visitADT(textElement()) = textElement();
public AstNode visitADT(memberRef()) = memberRef();
public AstNode visitADT(memberRefParameter()) = memberRefParameter();

public default AstNode visitADT(AstNode n) { println("AstNode pattern coverage: "); throw "<n>"; }
