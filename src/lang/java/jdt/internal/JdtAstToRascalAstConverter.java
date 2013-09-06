/*******************************************************************************
 * Copyright (c) 2009-2013 CWI
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *   * Jouke Stoel - Jouke.Stoel@cwi.nl (CWI)
 *   * Anastasia Izmaylova - A.Izmaylova@cwi.nl - CWI
*******************************************************************************/
package lang.java.jdt.internal;

import static org.rascalmpl.eclipse.library.lang.java.jdt.internal.Java.ADT_ENTITY;

import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import org.eclipse.imp.pdb.facts.IConstructor;
import org.eclipse.imp.pdb.facts.IMapWriter;
import org.eclipse.imp.pdb.facts.ISourceLocation;
import org.eclipse.imp.pdb.facts.IValue;
import org.eclipse.imp.pdb.facts.IValueFactory;
import org.eclipse.imp.pdb.facts.exceptions.UndeclaredConstructorException;
import org.eclipse.imp.pdb.facts.type.TypeFactory;
import org.eclipse.imp.pdb.facts.type.TypeStore;
import org.eclipse.jdt.core.dom.*;
import org.eclipse.jdt.core.dom.Modifier.ModifierKeyword;

@SuppressWarnings({"deprecation", "rawtypes"})
public class JdtAstToRascalAstConverter extends ASTVisitor {
//	private static final String ANNOTATION_JAVA_TYPE = "javaType";
	private static final String DATATYPE_OPTION = "Option";
	private static final String DATATYPE_RASCAL_AST_NODE = "AstNode";
	/*
	 * Richer binding information of a Java node
	 */
	public static final String ANNOTATION_JAVA_METHOD_BINDING = "methodBinding";
	public static final String ANNOTATION_JAVA_PACKAGE_BINDING = "packageBinding";
	public static final String ANNOTATION_JAVA_TYPE_BINDING = "typeBinding";
	public static final String ANNOTATION_JAVA_VARIABLE_BINDING = "variableBinding";
	public static final String ANNOTATION_JAVA_BINDINGS = "bindings";
	
	public static final String ANNOTATION_SOURCE_LOCATION = "location";
	
	private IValue ownValue;

	private final IValueFactory values;
	private final TypeStore typeStore;
	private static final TypeFactory TF = TypeFactory.getInstance();
	private final BindingConverter bindingConverter;	
	
	private CompilationUnit compilUnit;
	private ISourceLocation loc;

	private BindingsImporter bindingsImporter;
	
	private final org.eclipse.imp.pdb.facts.type.Type DATATYPE_RASCAL_AST_NODE_TYPE;
	private final org.eclipse.imp.pdb.facts.type.Type DATATYPE_OPTION_TYPE;
	private final Set<String> annotations;
	private final boolean collectBindings;

	
	public JdtAstToRascalAstConverter(final IValueFactory values, final TypeStore typeStore, final BindingConverter bindingConverter, boolean collectBindings) {
		this.values = values;
		this.typeStore = typeStore;
		this.bindingConverter = bindingConverter;
		this.bindingsImporter = new BindingsImporter(this.values, this.bindingConverter);
		this.DATATYPE_RASCAL_AST_NODE_TYPE = this.typeStore.lookupAbstractDataType(DATATYPE_RASCAL_AST_NODE);
		this.annotations = this.typeStore.getAnnotations(DATATYPE_RASCAL_AST_NODE_TYPE).keySet();
		this.DATATYPE_OPTION_TYPE = this.typeStore.lookupAbstractDataType(DATATYPE_OPTION);
		this.collectBindings = collectBindings;
	}
		
	public void set(CompilationUnit compilUnit) {
		this.compilUnit = compilUnit;
	}
	
	public void set(ISourceLocation loc) {
		this.loc = loc;
	}
	
	public BindingsImporter getBindingsImporter() {
		return this.bindingsImporter;
	}
	
	public IValue getValue() {
		return this.ownValue;
	}
	
	public void setRascalAstNodeAnnotation(String annoName, IValue annoValue) {
		if(this.ownValue == null) return ;
		if(this.ownValue.getType().equals(DATATYPE_RASCAL_AST_NODE_TYPE) && annotations.contains(annoName)) 
			this.ownValue = ((IConstructor) this.ownValue).asAnnotatable().setAnnotation(annoName, annoValue);
	}

	private IValueList parseModifiers(int modifiers) {
		IValueList modifierList = new IValueList(values);

		if (Modifier.isPublic(modifiers)) {
			modifierList.add(values.constructor(Java.CONS_PUBLIC)); 
		}
		if (Modifier.isProtected(modifiers)) {
			modifierList.add(values.constructor(Java.CONS_PROTECTED));
		}
		if (Modifier.isPrivate(modifiers)) {
			modifierList.add(values.constructor(Java.CONS_PRIVATE));
		}
		if (Modifier.isStatic(modifiers)) {
			modifierList.add(values.constructor(Java.CONS_STATIC));
		}
		if (Modifier.isAbstract(modifiers)) {
			modifierList.add(values.constructor(Java.CONS_ABSTRACT));
		}
		if (Modifier.isFinal(modifiers)) {
			modifierList.add(values.constructor(Java.CONS_FINAL));
		}
		if (Modifier.isSynchronized(modifiers)) {
			modifierList.add(values.constructor(Java.CONS_SYNCHRONIZED));
		}
		if (Modifier.isVolatile(modifiers)) {
			modifierList.add(values.constructor(Java.CONS_VOLATILE));
		}
		if (Modifier.isNative(modifiers)) {
			modifierList.add(values.constructor(Java.CONS_NATIVE));
		}
		if (Modifier.isStrictfp(modifiers)) {
			modifierList.add(values.constructor(Java.CONS_STRICTFP));
		}
		if (Modifier.isTransient(modifiers)) {
			modifierList.add(values.constructor(Java.CONS_TRANSIENT));
		}
		
		return modifierList;
	}

	private java.util.Map.Entry<IValueList, IValueList> parseExtendedModifiers(List ext) {
		IValueList modifierList = new IValueList(values);
		IValueList annotationsList = new IValueList(values);

		for (Iterator it = ext.iterator(); it.hasNext();) {
			ASTNode p = (ASTNode) it.next();
			if(p instanceof IExtendedModifier) {
				IValue val = visitChild(p);
				if(((IExtendedModifier) p).isModifier()) {
					modifierList.add(val);
				} else if(((IExtendedModifier) p).isAnnotation()) {
					annotationsList.add(val);
				}
			}
		}
		return new java.util.AbstractMap.SimpleEntry<IValueList, IValueList>(modifierList, annotationsList);
	}

	private java.util.Map.Entry<IValueList, IValueList> parseExtendedModifiers(BodyDeclaration node) {
		if (node.getAST().apiLevel() == AST.JLS2) {
			return new java.util.AbstractMap.SimpleEntry<IValueList, IValueList>(parseModifiers(node.getModifiers()), new IValueList(values));
		} else {
			return parseExtendedModifiers(node.modifiers());
		}
	}

	
	private IValue optional(IValue value) {
		if (value == null) {
			return none();
		} else {
			return some(value);
		}
	}
	
	private IValue none() {
		org.eclipse.imp.pdb.facts.type.Type constructor = typeStore.lookupConstructor(DATATYPE_OPTION_TYPE, "none", TF.tupleEmpty());
		if(constructor != null)
			return values.constructor(constructor, new IValue[] {});
			// DATATYPE_OPTION_TYPE.make(values, typeStore, "none", new IValue[] {});
		throw new UndeclaredConstructorException("none", TF.tupleEmpty());
	}
	
	private IValue some(IValue value) {
		org.eclipse.imp.pdb.facts.type.Type constructor = typeStore.lookupConstructor(DATATYPE_OPTION_TYPE, "some", TF.tupleType(value));
		if(constructor != null)
			return values.constructor(constructor, value);
		throw new UndeclaredConstructorException("some", TF.tupleType(value));
		// DATATYPE_OPTION_TYPE.make(values, typeStore, "some", value);		
	}

	private IValue visitChild(ASTNode node) {
		node.accept(this);

		return this.getValue();
	}

	private String getNodeName(ASTNode node) {
		return node.getClass().getSimpleName();
	}

	private IValue constructRascalNode(ASTNode node, IValue... children) {
		String constructorName = getNodeName(node);
		// Make sure that the constructor name starts with a lowercase character
		String modifiedConstructorName = constructorName.substring(0, 1).toLowerCase() + constructorName.substring(1);
		/*
		 *  Does not proper deal with possible initializers
		 *  
		if (rascalValue instanceof IConstructor) {
			IValue type = resolveType(node);

			if (type != null) {
				IConstructor rascalNode = (IConstructor) rascalValue;
				rascalValue = rascalNode.setAnnotation(ANNOTATION_JAVA_TYPE, type);
			}			
		}
		*/
		org.eclipse.imp.pdb.facts.type.Type constructor = typeStore.lookupConstructor(DATATYPE_RASCAL_AST_NODE_TYPE, modifiedConstructorName, TF.tupleType(children));
		if(constructor != null)
			return values.constructor(constructor, children);
		throw new UndeclaredConstructorException(modifiedConstructorName, TF.tupleType(children));
		// DATATYPE_RASCAL_AST_NODE_TYPE.make(values, typeStore, modifiedConstructorName, children);
	}
	/*
	private IValue resolveType(ASTNode node) {
		IValue type = null;
		
		if (node instanceof Type) {
			type = bindingConverter.getEntity(((Type) node).resolveBinding());
		} else if (node instanceof AbstractTypeDeclaration) {
			type = bindingConverter.getEntity(((AbstractTypeDeclaration) node).resolveBinding());
		} else if (node instanceof AnonymousClassDeclaration) {
			type = bindingConverter.getEntity(((AnonymousClassDeclaration) node).resolveBinding());
		} else if (node instanceof Expression) {
			type = (((Expression) node).resolveTypeBinding() != null) ? bindingConverter.getEntity(((Expression) node).resolveTypeBinding()) : null;
		} else if (node instanceof TypeDeclarationStatement) {
			type = bindingConverter.getEntity(((TypeDeclarationStatement) node).resolveBinding());
		} else if (node instanceof TypeParameter) {
			type = bindingConverter.getEntity(((TypeParameter) node).resolveBinding());
		} else if (node instanceof EnumDeclaration) {
			type = bindingConverter.getEntity(((EnumDeclaration) node).resolveBinding());
		} else if (node instanceof AnnotationTypeDeclaration) {
			type = bindingConverter.getEntity(((AnnotationTypeDeclaration) node).resolveBinding());
		}
		
		return type;
	}
	*/
	
//	private IValue constructRascalNode(String dataType, String constructorName, IValue... children) {
//		// Make sure that the constructor name starts with a lowercase character
//		String modifiedConstructorName = constructorName.substring(0, 1).toLowerCase() + constructorName.substring(1);
//		org.eclipse.imp.pdb.facts.type.Type type = typeStore.lookupAbstractDataType(dataType);
//		return type.make(values, typeStore, modifiedConstructorName, children);
//	}	

//	private IValue constructRascalNode(String dataType, String constructorName) {
//		org.eclipse.imp.pdb.facts.type.Type constructor = getConstructor(dataType, constructorName);
//		
//		return constructor.make(values);
//	}
//	
//	private org.eclipse.imp.pdb.facts.type.Type getConstructor(String dataType, String constructorName) {
//		org.eclipse.imp.pdb.facts.type.Type type = typeStore.lookupAbstractDataType(dataType);
//		
//		// Make sure that the constructor name starts with a lowercase character
//		String modifiedConstructorName = constructorName.substring(0, 1).toLowerCase() + constructorName.substring(1);
//		Set<org.eclipse.imp.pdb.facts.type.Type> constructors = typeStore.lookupConstructor(type, modifiedConstructorName);
//		
//		// There should be only one constructor. 
//		return constructors.iterator().next();
//	}
	
	/*
	 * 'preVisit' and 'postVisit' manage (scope) stacks of the bindingsImporter in a proper order
	 *  and resolve java bindings for a node if any
	 */
	public void preVisit(ASTNode node) {
		if(collectBindings) {
			bindingsImporter.resolveBindings(node);
			bindingsImporter.manageStacks(node, true);
		}
	}
	public void postVisit(ASTNode node) {
//		IValue javaType = bindingsImporter.popJavaType();
//		if(javaType != null) 
//			setRascalAstNodeAnnotation(ANNOTATION_JAVA_TYPE, javaType);
		if (collectBindings) {
			setRascalAstNodeAnnotation(ANNOTATION_JAVA_BINDINGS, bindingsImporter.popBindings());
			bindingsImporter.manageStacks(node, false);
		}
		int start = node.getStartPosition();
		int end = start + node.getLength() - 1;
		if(compilUnit != null && loc != null) 
			setRascalAstNodeAnnotation(ANNOTATION_SOURCE_LOCATION, values.sourceLocation(loc.getURI(), 
																			start, node.getLength(), 
																			compilUnit.getLineNumber(start), compilUnit.getLineNumber(end), 
																			compilUnit.getColumnNumber(start), compilUnit.getColumnNumber(end)));
		else System.err.println("The 'location' annotation can not be added to the node");
	}
	
	public boolean visit(AnnotationTypeDeclaration node) {
		java.util.Map.Entry<IValueList, IValueList> extendedModifiers = parseExtendedModifiers(node.modifiers());
		IValue name = values.string(node.getName().getFullyQualifiedName()); 
		
		IValueList bodyDeclarations = new IValueList(values);
		for (Iterator it = node.bodyDeclarations().iterator(); it.hasNext();) {
			BodyDeclaration d = (BodyDeclaration) it.next();
			bodyDeclarations.add(visitChild(d));
		}

		ownValue = constructRascalNode(node, extendedModifiers.getKey().asList(), extendedModifiers.getValue().asList(), 
										name, bodyDeclarations.asList());
		return false;
	}

	public boolean visit(AnnotationTypeMemberDeclaration node) {
		java.util.Map.Entry<IValueList, IValueList> extendedModifiers = parseExtendedModifiers(node.modifiers());
		IValue typeArgument = visitChild(node.getType());
		IValue name = values.string(node.getName().getFullyQualifiedName()); 
		IValue defaultBlock = node.getDefault() == null ? null : visitChild(node.getDefault());

		ownValue = constructRascalNode(node, extendedModifiers.getKey().asList(), extendedModifiers.getValue().asList(), 
										typeArgument, name, optional(defaultBlock));
		return false;
	}

	public boolean visit(AnonymousClassDeclaration node) {
		IValueList bodyDeclarations = new IValueList(values);

		for (Iterator it = node.bodyDeclarations().iterator(); it.hasNext();) {
			BodyDeclaration b = (BodyDeclaration) it.next();
			bodyDeclarations.add(visitChild(b));
		}

		ownValue = constructRascalNode(node, bodyDeclarations.asList());
		return false;
	}

	public boolean visit(ArrayAccess node) {
		IValue array = visitChild(node.getArray());
		IValue index = visitChild(node.getIndex());

		ownValue = constructRascalNode(node, array, index);
		return false;
	}

	public boolean visit(ArrayCreation node) {
		IValue type = visitChild(node.getType().getElementType());

		IValueList dimensions = new IValueList(values);
		for (Iterator it = node.dimensions().iterator(); it.hasNext();) {
			Expression e = (Expression) it.next();
			dimensions.add(visitChild(e));
		}

		IValue initializer = node.getInitializer() == null ? null : visitChild(node.getInitializer());

		ownValue = constructRascalNode(node, type, dimensions.asList(), optional(initializer));
		return false;
	}

	public boolean visit(ArrayInitializer node) {
		IValueList expressions = new IValueList(values);
		for (Iterator it = node.expressions().iterator(); it.hasNext();) {
			Expression e = (Expression) it.next();
			expressions.add(visitChild(e));
		}

		ownValue = constructRascalNode(node, expressions.asList());
		return false;
	}

	public boolean visit(ArrayType node) {
		IValue type = visitChild(node.getComponentType());
		ownValue = constructRascalNode(node, type);
		return false;
	}

	public boolean visit(AssertStatement node) {
		IValue expression = visitChild(node.getExpression());
		IValue message = node.getMessage() == null ? null : visitChild(node.getMessage());
	
		ownValue = constructRascalNode(node, expression, optional(message));
		return false;
	}

	public boolean visit(Assignment node) {
		IValue leftSide = visitChild(node.getLeftHandSide());
		IValue rightSide = visitChild(node.getRightHandSide());

		ownValue = constructRascalNode(node, leftSide, rightSide);
		return false;
	}

	public boolean visit(Block node) {
		IValueList statements = new IValueList(values);
		for (Iterator it = node.statements().iterator(); it.hasNext();) {
			Statement s = (Statement) it.next();
			statements.add(visitChild(s));
		}

		ownValue = constructRascalNode(node, statements.asList());
		return false;
	}

	public boolean visit(BlockComment node) {
		ownValue = constructRascalNode(node);
		return false;
	}

	public boolean visit(BooleanLiteral node) {
		IValue booleanValue = values.bool(node.booleanValue());

		ownValue = constructRascalNode(node, booleanValue);
		return false;
	}

	public boolean visit(BreakStatement node) {
		IValue label = node.getLabel() == null ? values.string("") : values.string(node.getLabel().getFullyQualifiedName());
		ownValue = constructRascalNode(node, optional(label));
		return false;
	}

	public boolean visit(CastExpression node) {
		IValue type = visitChild(node.getType());
		IValue expression = visitChild(node.getExpression());

		ownValue = constructRascalNode(node, type, expression);
		return false;
	}

	public boolean visit(CatchClause node) {
		IValue exception = visitChild(node.getException());
		IValue body = visitChild(node.getBody());

		ownValue = constructRascalNode(node, exception, body);
		return false;
	}

	public boolean visit(CharacterLiteral node) {
		IValue value = values.string(node.getEscapedValue()); 

		ownValue = constructRascalNode(node, value);
		return false;
	}
	
	public boolean visit(ClassInstanceCreation node) {
		IValue expression = node.getExpression() == null ? null : visitChild(node.getExpression());

		IValue type = null;
		IValueList genericTypes = new IValueList(values);
		if (node.getAST().apiLevel() == AST.JLS2) {
			type = visitChild(node.getName());
		} 
		else {
			type = visitChild(node.getType()); 

			if (!node.typeArguments().isEmpty()) {
				for (Iterator it = node.typeArguments().iterator(); it.hasNext();) {
					Type t = (Type) it.next();
					genericTypes.add(visitChild(t));
				}
			}
		}

		IValueList arguments = new IValueList(values);
		for (Iterator it = node.arguments().iterator(); it.hasNext();) {
			Expression e = (Expression) it.next();
			arguments.add(visitChild(e));
		}

		IValue anonymousClassDeclaration = node.getAnonymousClassDeclaration() == null ? null : visitChild(node.getAnonymousClassDeclaration());

		ownValue = constructRascalNode(node, optional(expression), type, genericTypes.asList(), arguments.asList(), optional(anonymousClassDeclaration));
		return false;
	}

	public boolean visit(CompilationUnit node) {
		IValue packageOfUnit = node.getPackage() == null ? null : visitChild(node.getPackage());

		IValueList imports = new IValueList(values);
		for (Iterator it = node.imports().iterator(); it.hasNext();) {
			ImportDeclaration d = (ImportDeclaration) it.next();
			imports.add(visitChild(d));
		}

		IValueList typeDeclarations = new IValueList(values);
		for (Iterator it = node.types().iterator(); it.hasNext();) {
			AbstractTypeDeclaration d = (AbstractTypeDeclaration) it.next();
			typeDeclarations.add(visitChild(d));
		}

		ownValue = constructRascalNode(node, optional(packageOfUnit), imports.asList(), typeDeclarations.asList());
		return false;
	}

	public boolean visit(ConditionalExpression node) {
		IValue expression = visitChild(node.getExpression());
		IValue thenBranch = visitChild(node.getThenExpression());
		IValue elseBranch = visitChild(node.getElseExpression());

		ownValue = constructRascalNode(node, expression, thenBranch, elseBranch);
		return false;
	}

	public boolean visit(ConstructorInvocation node) {
		IValueList types = new IValueList(values);
		if (node.getAST().apiLevel() >= AST.JLS3) {
			if (!node.typeArguments().isEmpty()) {

				for (Iterator it = node.typeArguments().iterator(); it.hasNext();) {
					Type t = (Type) it.next();
					types.add(visitChild(t));
				}
			}
		}

		IValueList arguments = new IValueList(values);
		for (Iterator it = node.arguments().iterator(); it.hasNext();) {
			Expression e = (Expression) it.next();
			arguments.add(visitChild(e));
		}

		ownValue = constructRascalNode(node, types.asList(), arguments.asList());
		return false;
	}

	public boolean visit(ContinueStatement node) {
		IValue label = node.getLabel() == null ? null : values.string(node.getLabel().getFullyQualifiedName());
		ownValue = constructRascalNode(node, optional(label));
		return false;
	}

	public boolean visit(DoStatement node) {
		IValue body = visitChild(node.getBody());
		IValue whileExpression = visitChild(node.getExpression());

		ownValue = constructRascalNode(node, body, whileExpression);
		return false;
	}

	public boolean visit(EmptyStatement node) {
		ownValue = constructRascalNode(node);
		return false;
	}

	public boolean visit(EnhancedForStatement node) {
		IValue parameter = visitChild(node.getParameter());
		IValue collectionExpression = visitChild(node.getExpression());
		IValue body = visitChild(node.getBody());

		ownValue = constructRascalNode(node, parameter, collectionExpression, body);
		return false;
	}

	public boolean visit(EnumConstantDeclaration node) {
		java.util.Map.Entry<IValueList, IValueList> extendedModifiers = parseExtendedModifiers(node.modifiers());
		IValue name = values.string(node.getName().getFullyQualifiedName()); 

		IValueList arguments = new IValueList(values);
		if (!node.arguments().isEmpty()) {
			for (Iterator it = node.arguments().iterator(); it.hasNext();) {
				Expression e = (Expression) it.next();
				arguments.add(visitChild(e));
			}
		}

		IValue anonymousClassDeclaration = node.getAnonymousClassDeclaration() == null ? null : visitChild(node.getAnonymousClassDeclaration());
		
		ownValue = constructRascalNode(node, extendedModifiers.getKey().asList(), extendedModifiers.getValue().asList(), 
										name, arguments.asList(), optional(anonymousClassDeclaration));
		return false;
	}

	public boolean visit(EnumDeclaration node) {
		java.util.Map.Entry<IValueList, IValueList> extendedModifiers = parseExtendedModifiers(node.modifiers());
		IValue name = values.string(node.getName().getFullyQualifiedName()); 

		IValueList implementedInterfaces = new IValueList(values);
		if (!node.superInterfaceTypes().isEmpty()) {
			for (Iterator it = node.superInterfaceTypes().iterator(); it.hasNext();) {
				Type t = (Type) it.next();
				implementedInterfaces.add(visitChild(t));
			}
		}

		IValueList enumConstants = new IValueList(values);
		for (Iterator it = node.enumConstants().iterator(); it.hasNext();) {
			EnumConstantDeclaration d = (EnumConstantDeclaration) it.next();
			enumConstants.add(visitChild(d));
		}

		IValueList bodyDeclarations = new IValueList(values);
		if (!node.bodyDeclarations().isEmpty()) {
			for (Iterator it = node.bodyDeclarations().iterator(); it.hasNext();) {
				BodyDeclaration d = (BodyDeclaration) it.next();
				bodyDeclarations.add(visitChild(d));
			}
		}

		ownValue = constructRascalNode(node, extendedModifiers.getKey().asList(), extendedModifiers.getValue().asList(), 
										name, implementedInterfaces.asList(), enumConstants.asList(), bodyDeclarations.asList());
		return false;
	}

	public boolean visit(ExpressionStatement node) {
		IValue expression = visitChild(node.getExpression());
		ownValue = constructRascalNode(node, expression);
		return false;
	}

	public boolean visit(FieldAccess node) {
		IValue expression = visitChild(node.getExpression());
		IValue name = values.string(node.getName().getFullyQualifiedName());

		ownValue = constructRascalNode(node, expression, name);
		return false;
	}

	public boolean visit(FieldDeclaration node) {
		java.util.Map.Entry<IValueList, IValueList> extendedModifiers = parseExtendedModifiers(node);
		IValue type = visitChild(node.getType());

		IValueList fragments = new IValueList(values);
		for (Iterator it = node.fragments().iterator(); it.hasNext();) {
			VariableDeclarationFragment f = (VariableDeclarationFragment) it.next();
			fragments.add(visitChild(f));
		}

		ownValue = constructRascalNode(node, extendedModifiers.getKey().asList(), extendedModifiers.getValue().asList(), 
										type, fragments.asList());
		return false;
	}

	public boolean visit(ForStatement node) {
		IValueList initializers = new IValueList(values);
		for (Iterator it = node.initializers().iterator(); it.hasNext();) {
			Expression e = (Expression) it.next();
			initializers.add(visitChild(e));
		}

		IValue booleanExpression = node.getExpression() == null ? null : visitChild(node.getExpression());

		IValueList updaters = new IValueList(values);
		for (Iterator it = node.updaters().iterator(); it.hasNext();) {
			Expression e = (Expression) it.next();
			updaters.add(visitChild(e));
		}

		IValue body = visitChild(node.getBody());

		ownValue = constructRascalNode(node, initializers.asList(), optional(booleanExpression), updaters.asList(), body);
		return false;
	}

	public boolean visit(IfStatement node) {
		IValue booleanExpression = visitChild(node.getExpression());
		IValue thenStatement = visitChild(node.getThenStatement());
		IValue elseStatement = node.getElseStatement() == null ? null : visitChild(node.getElseStatement());

		ownValue = constructRascalNode(node, booleanExpression, thenStatement, optional(elseStatement));
		return false;
	}

	public boolean visit(ImportDeclaration node) {
		IValue name = values.string(node.getName().getFullyQualifiedName());

		IValue staticImport = values.bool(false);
		if (node.getAST().apiLevel() >= AST.JLS3) {
			staticImport = values.bool(node.isStatic());
		}
		IValue onDemand = values.bool(node.isOnDemand());

		ownValue = constructRascalNode(node, name, staticImport, onDemand); 
		return false;
	}

	public boolean visit(InfixExpression node) {
		IValue operator = values.string(node.getOperator().toString());
		IValue leftSide = visitChild(node.getLeftOperand());
		IValue rightSide = visitChild(node.getRightOperand());

		IValueList extendedOperands = new IValueList(values);
		if (node.hasExtendedOperands()) {
			for (Iterator it = node.extendedOperands().iterator(); it.hasNext();) {
				Expression e = (Expression) it.next();
				extendedOperands.add(visitChild(e));
			}
		}

		ownValue = constructRascalNode(node, operator, leftSide, rightSide, extendedOperands.asList());
		return false;
	}

	public boolean visit(Initializer node) {
		java.util.Map.Entry<IValueList, IValueList> extendedModifiers = parseExtendedModifiers(node);
		IValue body = visitChild(node.getBody());

		ownValue = constructRascalNode(node, extendedModifiers.getKey().asList(), extendedModifiers.getValue().asList(), body);
		return false;
	}

	public boolean visit(InstanceofExpression node) {
		IValue leftSide = visitChild(node.getLeftOperand());
		IValue rightSide = visitChild(node.getRightOperand());

		ownValue = constructRascalNode(node, leftSide, rightSide);
		return false;
	}

	public boolean visit(Javadoc node) {
		ownValue = constructRascalNode(node);
		return false;
	}

	public boolean visit(LabeledStatement node) {
		IValue label = values.string(node.getLabel().getFullyQualifiedName());
		IValue body = visitChild(node.getBody());

		ownValue = constructRascalNode(node, label, body);
		return false;
	}

	public boolean visit(LineComment node) {
		ownValue = constructRascalNode(node);
		return false;
	}

	public boolean visit(MarkerAnnotation node) {
		IValue typeName = values.string(node.getTypeName().getFullyQualifiedName());
		ownValue = constructRascalNode(node, typeName);
		return false;
	}

	public boolean visit(MemberRef node) {
		return false;
	}

	public boolean visit(MemberValuePair node) {
		IValue name = values.string(node.getName().getFullyQualifiedName());
		IValue value = visitChild(node.getValue());

		ownValue = constructRascalNode(node, name, value);
		return false;
	}

	public boolean visit(MethodDeclaration node) {
		java.util.Map.Entry<IValueList, IValueList> extendedModifiers = parseExtendedModifiers(node);
		
		IValueList genericTypes = new IValueList(values);
		if (node.getAST().apiLevel() >= AST.JLS3) {
			if (!node.typeParameters().isEmpty()) {
				for (Iterator it = node.typeParameters().iterator(); it.hasNext();) {
					TypeParameter t = (TypeParameter) it.next();
					genericTypes.add(visitChild(t));
				}
			}
		}

		IValue returnType = null;
		if (!node.isConstructor()) {
			if (node.getAST().apiLevel() == AST.JLS2) {
				returnType = visitChild(node.getReturnType());
			} else if (node.getReturnType2() != null) {
				returnType = visitChild(node.getReturnType2());
			} else {
				// methods really ought to have a return type
				returnType = values.constructor(Java.CONS_VOID);
			}
		}

		IValue name = values.string(node.getName().getFullyQualifiedName());

		IValueList parameters = new IValueList(values);
		for (Iterator it = node.parameters().iterator(); it.hasNext();) {
			SingleVariableDeclaration v = (SingleVariableDeclaration) it.next();
			parameters.add(visitChild(v));
		}

		/*
		 * for (int i = 0; i < node.getExtraDimensions(); i++) {
		 * //this.buffer.append("[]"); //$NON-NLS-1$ // TODO: Do these need to be included in the node tree? 
		 * }
		 */

		IValueList possibleExceptions = new IValueList(values);
		if (!node.thrownExceptions().isEmpty()) {

			for (Iterator it = node.thrownExceptions().iterator(); it.hasNext();) {
				Name n = (Name) it.next();
				possibleExceptions.add(visitChild(n));
			}
		}

		IValue body = node.getBody() == null ? null : visitChild(node.getBody()); 

		ownValue = constructRascalNode(node, extendedModifiers.getKey().asList(), extendedModifiers.getValue().asList(), 
									genericTypes.asList(), optional(returnType), name, parameters.asList(), possibleExceptions.asList(), optional(body));
		return false;
	}

	public boolean visit(MethodInvocation node) {
		IValue expression = node.getExpression() == null ? null : visitChild(node.getExpression());
		
		IValueList genericTypes = new IValueList(values);
		if (node.getAST().apiLevel() >= AST.JLS3) {
			if (!node.typeArguments().isEmpty()) {
				for (Iterator it = node.typeArguments().iterator(); it.hasNext();) {
					Type t = (Type) it.next();
					genericTypes.add(visitChild(t));
				}
			}
		}

		IValue name = values.string(node.getName().getFullyQualifiedName());

		IValueList arguments = new IValueList(values);
		for (Iterator it = node.arguments().iterator(); it.hasNext();) {
			Expression e = (Expression) it.next();
			arguments.add(visitChild(e));
		}		
		
		ownValue = constructRascalNode(node, optional(expression), genericTypes.asList(), name, arguments.asList());
		return false;
	}

	public boolean visit(MethodRef node) {
		return false;
	}

	public boolean visit(MethodRefParameter node) {
		return false;
	}

	public boolean visit(Modifier node) {
		if (node.getKeyword().equals(ModifierKeyword.PUBLIC_KEYWORD)) {
			ownValue = values.constructor(Java.CONS_PUBLIC); 
		} else if (node.getKeyword().equals(ModifierKeyword.PROTECTED_KEYWORD)) {
			ownValue = values.constructor(Java.CONS_PROTECTED);
		} else if (node.getKeyword().equals(ModifierKeyword.PRIVATE_KEYWORD)) {
			ownValue = values.constructor(Java.CONS_PRIVATE);
		} else if (node.getKeyword().equals(ModifierKeyword.STATIC_KEYWORD)) {
			ownValue = values.constructor(Java.CONS_STATIC);
		} else if (node.getKeyword().equals(ModifierKeyword.ABSTRACT_KEYWORD)) {
			ownValue = values.constructor(Java.CONS_ABSTRACT);
		} else if (node.getKeyword().equals(ModifierKeyword.FINAL_KEYWORD)) {
			ownValue = values.constructor(Java.CONS_FINAL);
		} else if (node.getKeyword().equals(ModifierKeyword.SYNCHRONIZED_KEYWORD)) {
			ownValue = values.constructor(Java.CONS_SYNCHRONIZED);
		} else if (node.getKeyword().equals(ModifierKeyword.VOLATILE_KEYWORD)) {
			ownValue = values.constructor(Java.CONS_VOLATILE);
		} else if (node.getKeyword().equals(ModifierKeyword.NATIVE_KEYWORD)) {
			ownValue = values.constructor(Java.CONS_NATIVE);
		} else if (node.getKeyword().equals(ModifierKeyword.STRICTFP_KEYWORD)) {
			ownValue = values.constructor(Java.CONS_STRICTFP);
		} else if (node.getKeyword().equals(ModifierKeyword.TRANSIENT_KEYWORD)) {
			ownValue = values.constructor(Java.CONS_TRANSIENT);
		}

		return false;
	}

	public boolean visit(NormalAnnotation node) {
		IValue typeName = values.string(node.getTypeName().getFullyQualifiedName());

		IValueList memberValuePairs = new IValueList(values);
		for (Iterator it = node.values().iterator(); it.hasNext();) {
			MemberValuePair p = (MemberValuePair) it.next();
			memberValuePairs.add(visitChild(p));
		}

		ownValue = constructRascalNode(node, typeName, memberValuePairs.asList());
		return false;
	}

	public boolean visit(NullLiteral node) {
		ownValue = constructRascalNode(node);
		return false;
	}

	public boolean visit(NumberLiteral node) {
		IValue number = values.string(node.getToken());

		ownValue = constructRascalNode(node, number);
		return false;
	}

	public boolean visit(PackageDeclaration node) {
		IValue name = values.string(node.getName().getFullyQualifiedName());
		
		IValueList annotations = new IValueList(values);
		if (node.getAST().apiLevel() >= AST.JLS3) {
			for (Iterator it = node.annotations().iterator(); it.hasNext();) {
				Annotation p = (Annotation) it.next();
				annotations.add(visitChild(p));
			}
		}

		ownValue = constructRascalNode(node, name, annotations.asList());
		return false;
	}

	public boolean visit(ParameterizedType node) {
		IValue type = visitChild(node.getType());

		IValueList genericTypes = new IValueList(values);
		for (Iterator it = node.typeArguments().iterator(); it.hasNext();) {
			Type t = (Type) it.next();
			genericTypes.add(visitChild(t));
		}

		ownValue = constructRascalNode(node, type, genericTypes.asList());
		return false;
	}

	public boolean visit(ParenthesizedExpression node) {
		IValue expression = visitChild(node.getExpression());
		ownValue = constructRascalNode(node, expression);
		return false;
	}

	public boolean visit(PostfixExpression node) {
		IValue operand = visitChild(node.getOperand());
		IValue operator = values.string(node.getOperator().toString());

		ownValue = constructRascalNode(node, operand, operator);
		return false;
	}

	public boolean visit(PrefixExpression node) {
		IValue operand = visitChild(node.getOperand());
		IValue operator = values.string(node.getOperator().toString());

		ownValue = constructRascalNode(node, operand, operator);
		return false;
	}

	public boolean visit(PrimitiveType node) {
		IValue type;
		
		if (node.getPrimitiveTypeCode().equals(PrimitiveType.BOOLEAN)) {
			type = values.constructor(Java.CONS_BOOLEAN);
		} else if (node.getPrimitiveTypeCode().equals(PrimitiveType.BYTE)) {
			type = values.constructor(Java.CONS_BYTE);
		} else if (node.getPrimitiveTypeCode().equals(PrimitiveType.CHAR)) {
			type = values.constructor(Java.CONS_CHAR);
		} else if (node.getPrimitiveTypeCode().equals(PrimitiveType.DOUBLE)) {
			type = values.constructor(Java.CONS_DOUBLE);
		} else if (node.getPrimitiveTypeCode().equals(PrimitiveType.FLOAT)) {
			type = values.constructor(Java.CONS_FLOAT);
		} else if (node.getPrimitiveTypeCode().equals(PrimitiveType.INT)) {
			type = values.constructor(Java.CONS_INT);
		} else if (node.getPrimitiveTypeCode().equals(PrimitiveType.LONG)) {
			type = values.constructor(Java.CONS_LONG);
		} else if (node.getPrimitiveTypeCode().equals(PrimitiveType.SHORT)) {
			type = values.constructor(Java.CONS_SHORT);
		} else {
			type = values.constructor(Java.CONS_VOID);
		}			
				
		ownValue = constructRascalNode(node, type);
		return false;
	}

	public boolean visit(QualifiedName node) {
		IValue qualifier = visitChild(node.getQualifier());
		IValue name = values.string((node.getName().getFullyQualifiedName()));
		ownValue = constructRascalNode(node, qualifier, name);
		return false;
	}

	public boolean visit(QualifiedType node) {
		IValue qualifier = visitChild(node.getQualifier());
		IValue name = values.string((node.getName().getFullyQualifiedName()));

		ownValue = constructRascalNode(node, qualifier, name);
		return false;
	}
	
	public boolean visit(ReturnStatement node) {
		IValue expression = node.getExpression() == null ? null : visitChild(node.getExpression());
		ownValue = constructRascalNode(node, optional(expression));
		return false;
	}

	public boolean visit(SimpleName node) {
		IValue value = values.string(node.getFullyQualifiedName());
		ownValue = constructRascalNode(node, value);
		return false;
	}

	public boolean visit(SimpleType node) {
		IValue type = values.string(node.getName().getFullyQualifiedName());
		ownValue = constructRascalNode(node, type);
		return false;
	}

	public boolean visit(SingleMemberAnnotation node) {
		IValue name = values.string(node.getTypeName().getFullyQualifiedName());
		IValue value = visitChild(node.getValue());

		ownValue = constructRascalNode(node, name, value);
		return false;
	}

	public boolean visit(SingleVariableDeclaration node) {
		IValue name = values.string(node.getName().getFullyQualifiedName());

		java.util.Map.Entry<IValueList, IValueList> extendedModifiers;
		if (node.getAST().apiLevel() == AST.JLS2) {
			extendedModifiers = new java.util.AbstractMap.SimpleEntry<IValueList, IValueList>(parseModifiers(node.getModifiers()), new IValueList(values));
		} else {
			extendedModifiers = parseExtendedModifiers(node.modifiers());
			
		}

		IValue type = visitChild(node.getType());
		IValue initializer = node.getInitializer() == null ? null : visitChild(node.getInitializer());

		IValue isVarags = values.bool(false);
		if (node.getAST().apiLevel() >= AST.JLS3) {
			isVarags = values.bool(node.isVarargs());
		}

		/*
		 * for (int i = 0; i < node.getExtraDimensions(); i++) { 
		 * //TODO: What todo with the extra dimensions... 
		 * 		this.buffer.append("[]");
		 * //$NON-NLS-1$ }
		 */

		ownValue = constructRascalNode(node, name, extendedModifiers.getKey().asList(), extendedModifiers.getValue().asList(), 
										type, optional(initializer), isVarags);
		return false;
	}

	public boolean visit(StringLiteral node) {
		IValue value = values.string(node.getEscapedValue());		
		ownValue = constructRascalNode(node, value);
		return false;
	}

	public boolean visit(SuperConstructorInvocation node) {
		IValue expression = node.getExpression() == null ? null : visitChild(node.getExpression());

		IValueList genericTypes = new IValueList(values);	
		if (node.getAST().apiLevel() >= AST.JLS3) {
			if (!node.typeArguments().isEmpty()) {
				for (Iterator it = node.typeArguments().iterator(); it.hasNext();) {
					Type t = (Type) it.next();
					genericTypes.add(visitChild(t));
				}
			}
		}

		IValueList arguments = new IValueList(values);
		for (Iterator it = node.arguments().iterator(); it.hasNext();) {
			Expression e = (Expression) it.next();
			arguments.add(visitChild(e));
		}

		ownValue = constructRascalNode(node, optional(expression), genericTypes.asList(), arguments.asList());
		return false;
	}

	public boolean visit(SuperFieldAccess node) {
		IValue qualifier = node.getQualifier() == null ? null : visitChild(node.getQualifier());
		IValue name = values.string((node.getName().getFullyQualifiedName()));

		ownValue = constructRascalNode(node, optional(qualifier), name);
		return false;
	}

	public boolean visit(SuperMethodInvocation node) {
		IValue qualifier = node.getQualifier() == null ? null : visitChild(node.getQualifier());
		
		IValueList genericTypes = new IValueList(values);
		if (node.getAST().apiLevel() >= AST.JLS3) {
			if (!node.typeArguments().isEmpty()) {
				for (Iterator it = node.typeArguments().iterator(); it.hasNext();) {
					Type t = (Type) it.next();
					genericTypes.add(visitChild(t));
				}
			}
		}

		IValue name = values.string(node.getName().getFullyQualifiedName());

		IValueList arguments = new IValueList(values);
		for (Iterator it = node.arguments().iterator(); it.hasNext();) {
			Expression e = (Expression) it.next();
			arguments.add(visitChild(e));
		}

		ownValue = constructRascalNode(node, optional(qualifier), genericTypes.asList(), name, arguments.asList());
		return false;
	}

	public boolean visit(SwitchCase node) {
		IValue isDefault = values.bool(node.isDefault());
		IValue expression = node.getExpression() == null ? null : visitChild(node.getExpression());

		ownValue = constructRascalNode(node, isDefault, optional(expression));
		return false;
	}

	public boolean visit(SwitchStatement node) {
		IValue expression = visitChild(node.getExpression());

		IValueList statements = new IValueList(values);
		for (Iterator it = node.statements().iterator(); it.hasNext();) {
			Statement s = (Statement) it.next();
			statements.add(visitChild(s));
		}

		ownValue = constructRascalNode(node, expression, statements.asList());
		return false;
	}

	public boolean visit(SynchronizedStatement node) {
		IValue expression = visitChild(node.getExpression());
		IValue body = visitChild(node.getBody());
		
		ownValue = constructRascalNode(node, expression, body);
		return false;
	}

	public boolean visit(TagElement node) {
		// TODO: What to do with JavaDoc?
		return false;
	}

	public boolean visit(TextElement node) {
		// TODO: What to do with JavaDoc?
		return false;
	}

	public boolean visit(ThisExpression node) {
		IValue qualifier = node.getQualifier() == null ? null : visitChild(node.getQualifier());

		ownValue = constructRascalNode(node, optional(qualifier));
		return false;
	}

	public boolean visit(ThrowStatement node) {
		IValue expression = visitChild(node.getExpression());
		
		ownValue = constructRascalNode(node, expression);
		return false;
	}

	public boolean visit(TryStatement node) {
		IValue body = visitChild(node.getBody());

		IValueList catchClauses = new IValueList(values);
		for (Iterator it = node.catchClauses().iterator(); it.hasNext();) {
			CatchClause cc = (CatchClause) it.next();
			catchClauses.add(visitChild(cc));
		}
		
		IValue finallyBlock = node.getFinally() == null ? null : visitChild(node.getFinally()); 
		
		ownValue = constructRascalNode(node, body, catchClauses.asList(), optional(finallyBlock));
		return false;
	}

	public boolean visit(TypeDeclaration node) {
		java.util.Map.Entry<IValueList, IValueList> extendedModifiers = parseExtendedModifiers(node);
		IValue objectType = node.isInterface() ? values.string("interface") : values.string("class");
		IValue name = values.string(node.getName().getFullyQualifiedName()); 
		
		IValueList genericTypes = new IValueList(values);
		if (node.getAST().apiLevel() >= AST.JLS3) {
			if (!node.typeParameters().isEmpty()) {			
				for (Iterator it = node.typeParameters().iterator(); it.hasNext();) {
					TypeParameter t = (TypeParameter) it.next();
					genericTypes.add(visitChild(t));			
				}
			}
		}
		
		IValue extendsClass = null;
		IValueList implementsInterfaces = new IValueList(values);
		
		if (node.getAST().apiLevel() == AST.JLS2) {
			if (node.getSuperclass() != null) {
				extendsClass = visitChild(node.getSuperclass());
			}
			if (!node.superInterfaces().isEmpty()) {
				for (Iterator it = node.superInterfaces().iterator(); it.hasNext();) {
					Name n = (Name) it.next();
					implementsInterfaces.add(visitChild(n));
				}
			}
		} else if (node.getAST().apiLevel() >= AST.JLS3) {
			if (node.getSuperclassType() != null) {
				extendsClass = visitChild(node.getSuperclassType());
			}
			if (!node.superInterfaceTypes().isEmpty()) {
				for (Iterator it = node.superInterfaceTypes().iterator(); it.hasNext();) {
					Type t = (Type) it.next();
					implementsInterfaces.add(visitChild(t));
				}
			}
		}

		IValueList bodyDeclarations = new IValueList(values);
		for (Iterator it = node.bodyDeclarations().iterator(); it.hasNext();) {
			BodyDeclaration d = (BodyDeclaration) it.next();
			bodyDeclarations.add(visitChild(d));
		}
		
		ownValue = constructRascalNode(node, extendedModifiers.getKey().asList(), extendedModifiers.getValue().asList(), 
										objectType, name, genericTypes.asList(), optional(extendsClass), implementsInterfaces.asList(), bodyDeclarations.asList());
		return false;
	}

	public boolean visit(TypeDeclarationStatement node) {
		IValue typeDeclaration;
		if (node.getAST().apiLevel() == AST.JLS2) {
			typeDeclaration = visitChild(node.getTypeDeclaration());
		}
		else {
			typeDeclaration = visitChild(node.getDeclaration());
		}
		
		ownValue = constructRascalNode(node, typeDeclaration);
		return false;
	}

	public boolean visit(TypeLiteral node) {
		IValue type = visitChild(node.getType());

		ownValue = constructRascalNode(node, type);
		return false;
	}

	public boolean visit(TypeParameter node) {
		IValue name = values.string(node.getName().getFullyQualifiedName());
		
		IValueList extendsList = new IValueList(values);
		if (!node.typeBounds().isEmpty()) {
			for (Iterator it = node.typeBounds().iterator(); it.hasNext();) {
				Type t = (Type) it.next();
				extendsList.add(visitChild(t));
			}
		}
		
		ownValue = constructRascalNode(node, name, extendsList.asList());
		return false;
	}
	
	public boolean visit(UnionType node) {
		IValueList typesValues = new IValueList(values);
		for(Iterator types = node.types().iterator(); types.hasNext();) {
			Type type = (Type) types.next();
			typesValues.add(visitChild(type));
		}
		
		ownValue = constructRascalNode(node, typesValues.asList());
		return false;
	}

	public boolean visit(VariableDeclarationExpression node) {

		java.util.Map.Entry<IValueList, IValueList> extendedModifiers;
		if (node.getAST().apiLevel() == AST.JLS2) {
			extendedModifiers = new java.util.AbstractMap.SimpleEntry<IValueList, IValueList>(parseModifiers(node.getModifiers()), new IValueList(values));
		} else {
			extendedModifiers = parseExtendedModifiers(node.modifiers());
		}
		
		IValue type = visitChild(node.getType());
		
		IValueList fragments = new IValueList(values);
		for (Iterator it = node.fragments().iterator(); it.hasNext();) {
			VariableDeclarationFragment f = (VariableDeclarationFragment) it.next();
			fragments.add(visitChild(f));
		}
		
		ownValue = constructRascalNode(node, extendedModifiers.getKey().asList(), extendedModifiers.getValue().asList(), 
										type, fragments.asList());
		return false;
	}

	public boolean visit(VariableDeclarationFragment node) {
		IValue name = values.string(node.getName().getFullyQualifiedName());
		
		//TODO: Extra dimensions?
		/*for (int i = 0; i < node.getExtraDimensions(); i++) {
			this.buffer.append("[]");//$NON-NLS-1$
		}*/
		
		IValue initializer = node.getInitializer() == null ? null : visitChild(node.getInitializer());

		ownValue = constructRascalNode(node, name, optional(initializer));
		return false;
	}

	public boolean visit(VariableDeclarationStatement node) {
		java.util.Map.Entry<IValueList, IValueList> extendedModifiers;
		if (node.getAST().apiLevel() == AST.JLS2) {
			extendedModifiers = new java.util.AbstractMap.SimpleEntry<IValueList, IValueList>(parseModifiers(node.getModifiers()), new IValueList(values));
		} else {		
			extendedModifiers = parseExtendedModifiers(node.modifiers());
		}
		
		IValue type = visitChild(node.getType());

		IValueList fragments = new IValueList(values);
		for (Iterator it = node.fragments().iterator(); it.hasNext();) {
			VariableDeclarationFragment f = (VariableDeclarationFragment) it.next();
			fragments.add(visitChild(f));
		}
		
		ownValue = constructRascalNode(node, extendedModifiers.getKey().asList(), extendedModifiers.getValue().asList(), 
										type, fragments.asList());
		return false;
	}

	public boolean visit(WhileStatement node) {
		IValue expression = visitChild(node.getExpression());
		IValue body = visitChild(node.getBody());
		
		ownValue = constructRascalNode(node, expression, body);
		return false;
	}

	public boolean visit(WildcardType node) {
		IValue type = null;
		IValue bound = null;
		
		if (node.getBound() != null) {
			type = visitChild(node.getBound());
			
			if (node.isUpperBound()) {
				bound = values.string(Java.CONS_EXTENDS.getName());
				
			} else {
				bound = values.string(Java.CONS_SUPER.getName());
			}
		}

		ownValue = constructRascalNode(node, optional(type), optional(bound));
		return false;
	}
	
	/*
	 *  Inner class to resolve various java bindings
	 *  An object manages scope stacks and imports possible bindings
	 */
	static public class BindingsImporter extends BindingsResolver {
		
//		private IValue javaType;
		private IMapWriter bindings;
		
//		private final Stack<IValue> javaTypeStack;
		private final Stack<IValue> bindingsStack;
		
		private TypeFactory ftypes = TypeFactory.getInstance();
		private final IValueFactory values;
		private final BindingConverter bindingConverter;
		
		public BindingsImporter(final IValueFactory values, final BindingConverter bindingConverter) {
			super(bindingConverter);
			this.values = values;
			this.bindingConverter = bindingConverter;
			
//			this.javaTypeStack = new Stack<IValue>();
			this.bindingsStack = new Stack<IValue>();			
		}
				
//		public IValue popJavaType() {
//			return this.javaTypeStack.pop();
//		}
		
		public IValue popBindings() {
			return this.bindingsStack.pop();
		}
		
		private void pushAllBindings() {
//			javaTypeStack.push(javaType);
			bindingsStack.push(bindings.done());
		}
		
		public void resolveBindings(ASTNode node) {
//			this.javaType = null;
			this.bindings = this.values.mapWriter(this.ftypes.stringType(), ADT_ENTITY);
			super.resolveBindings(node);
			this.pushAllBindings();
		}
		public void importBinding(IMethodBinding binding) {
			this.bindings.put(this.values.string(ANNOTATION_JAVA_METHOD_BINDING), this.bindingConverter.getEntity(binding));
		}
		public void importBinding(IPackageBinding binding) {
			this.bindings.put(this.values.string(ANNOTATION_JAVA_PACKAGE_BINDING), this.bindingConverter.getEntity(binding));
		}
		public void importBinding(ITypeBinding binding, Initializer initializer) {
//			this.javaType = this.bindingConverter.getEntity(binding, initializer);
//			this.bindings.put(this.values.string(ANNOTATION_JAVA_TYPE_BINDING), this.javaType);
			this.bindings.put(this.values.string(ANNOTATION_JAVA_TYPE_BINDING), this.bindingConverter.getEntity(binding, initializer));
		}
		public void importBinding(IVariableBinding binding, Initializer initializer) {
			this.bindings.put(this.values.string(ANNOTATION_JAVA_VARIABLE_BINDING), this.bindingConverter.getEntity(binding, initializer));
		}
	}

}