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

import org.eclipse.imp.pdb.facts.IValueFactory;
import org.eclipse.imp.pdb.facts.type.TypeStore;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ITypeBinding;

/*
 * Extends the JdtAstToRascalAstConverter to annotate a node with the scope information (refactoring-specific)
 */
public class JdtAstToRascalAstConverter extends org.rascalmpl.eclipse.library.lang.java.jdt.internal.JdtAstToRascalAstConverter {
	
	public JdtAstToRascalAstConverter(final IValueFactory values, final TypeStore typeStore, final BindingConverter bindingConverter) {
		super(values, typeStore, bindingConverter);
	}
	
	public static final String ANNOTATION_SCOPE = "scope";
	
	private ITypeBinding scope;
	
	public void preVisit(ASTNode node) {
		super.preVisit(node);
		scope = this.getBindingsImporter().getEnclosingType();
	}
		
	public void postVisit(ASTNode node) {
		super.postVisit(node);
		if(scope != null) 
			this.setRascalAstNodeAnnotation(ANNOTATION_SCOPE, this.getBindingsImporter().getBindingConverter().getEntity(this.scope));
	}
}
