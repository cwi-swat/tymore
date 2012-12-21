/*******************************************************************************
 * Copyright (c) 2009-2012 CWI
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *   * Anastasia Izmaylova - A.Izmaylova@cwi.nl (CWI)
*******************************************************************************/
package prototype.org.rascalmpl.eclipse.library.lang.java.jdt.refactorings.internal;

import org.eclipse.jdt.core.dom.ArrayAccess;
import org.eclipse.jdt.core.dom.ArrayCreation;
import org.eclipse.jdt.core.dom.ArrayInitializer;
import org.eclipse.jdt.core.dom.Assignment;
import org.eclipse.jdt.core.dom.BooleanLiteral;
import org.eclipse.jdt.core.dom.CastExpression;
import org.eclipse.jdt.core.dom.CharacterLiteral;
import org.eclipse.jdt.core.dom.ClassInstanceCreation;
import org.eclipse.jdt.core.dom.ConditionalExpression;
import org.eclipse.jdt.core.dom.ConstructorInvocation;
import org.eclipse.jdt.core.dom.FieldAccess;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.InfixExpression;
import org.eclipse.jdt.core.dom.InstanceofExpression;
import org.eclipse.jdt.core.dom.MarkerAnnotation;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.NormalAnnotation;
import org.eclipse.jdt.core.dom.NullLiteral;
import org.eclipse.jdt.core.dom.NumberLiteral;
import org.eclipse.jdt.core.dom.ParenthesizedExpression;
import org.eclipse.jdt.core.dom.PostfixExpression;
import org.eclipse.jdt.core.dom.PrefixExpression;
import org.eclipse.jdt.core.dom.QualifiedName;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SingleMemberAnnotation;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.StringLiteral;
import org.eclipse.jdt.core.dom.SuperConstructorInvocation;
import org.eclipse.jdt.core.dom.SuperFieldAccess;
import org.eclipse.jdt.core.dom.SuperMethodInvocation;
import org.eclipse.jdt.core.dom.ThisExpression;
import org.eclipse.jdt.core.dom.TypeLiteral;
import org.eclipse.jdt.core.dom.VariableDeclarationExpression;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;

public interface IExpressionTypeBindingResolver {
	
	// expression
	public IBinding resolveTypeBinding(ArrayAccess node);
	// expression
	public IBinding resolveTypeBinding(ArrayCreation node);
	// expression
	public IBinding resolveTypeBinding(ArrayInitializer node);
	// expression
	public IBinding resolveTypeBinding(Assignment node);
	// expression
	public IBinding resolveTypeBinding(BooleanLiteral node);
	// expression
	public IBinding resolveTypeBinding(CastExpression node);
	// expression
	public IBinding resolveTypeBinding(CharacterLiteral node);
	// expression
	public IBinding resolveTypeBinding(ClassInstanceCreation node);
	// expression
	public IBinding resolveTypeBinding(ConditionalExpression node);
	// statement
	public IBinding resolveTypeBinding(ConstructorInvocation node);
	// expression
	public IBinding resolveTypeBinding(FieldAccess node);
	// expression
	public IBinding resolveTypeBinding(InfixExpression node);
	// expression
	public IBinding resolveTypeBinding(InstanceofExpression node);
	// expression
	public IBinding resolveTypeBinding(MarkerAnnotation node);
	// expression
	public IBinding resolveTypeBinding(MethodInvocation node);
	// expression
	public IBinding resolveTypeBinding(NormalAnnotation node);
	// expression
	public IBinding resolveTypeBinding(NullLiteral node);
	// expression
	public IBinding resolveTypeBinding(NumberLiteral node);
	// expression
	public IBinding resolveTypeBinding(ParenthesizedExpression node);
	// expression
	public IBinding resolveTypeBinding(PostfixExpression node);
	// expression
	public IBinding resolveTypeBinding(PrefixExpression node);
	// expression
	public IBinding resolveTypeBinding(QualifiedName node);
	// expression
	public IBinding resolveTypeBinding(SimpleName node);
	// expression
	public IBinding resolveTypeBinding(SingleMemberAnnotation node);
	// expression
	public IBinding resolveTypeBinding(SingleVariableDeclaration node);
	// expression
	public IBinding resolveTypeBinding(StringLiteral node);
	// statement
	public IBinding resolveTypeBinding(SuperConstructorInvocation node);
	// expression
	public IBinding resolveTypeBinding(SuperFieldAccess node);
	// expression
	public IBinding resolveTypeBinding(SuperMethodInvocation node);
	// expression
	public IBinding resolveTypeBinding(ThisExpression node);
	// expression
	public IBinding resolveTypeBinding(TypeLiteral node);
	// expression
	public IBinding resolveTypeBinding(VariableDeclarationExpression node);
	// declaration
	public IBinding resolveTypeBinding(VariableDeclarationFragment node);
}
