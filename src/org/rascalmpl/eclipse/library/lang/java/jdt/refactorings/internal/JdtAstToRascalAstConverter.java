/*******************************************************************************
 * Copyright (c) 2009-2011 CWI
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *   * Anastasia Izmaylova - A.Izmaylova@cwi.nl (CWI)
*******************************************************************************/
package org.rascalmpl.eclipse.library.lang.java.jdt.refactorings.internal;

import org.eclipse.imp.pdb.facts.ISourceLocation;
import org.eclipse.imp.pdb.facts.IValueFactory;
import org.eclipse.imp.pdb.facts.type.TypeStore;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.ITypeBinding;

/*
 * Extends the JdtAstToRascalAstConverter to annotate a node with the location and scope information (refactoring-specific)
 */
public class JdtAstToRascalAstConverter extends org.rascalmpl.eclipse.library.lang.java.jdt.internal.JdtAstToRascalAstConverter {
	
	public static final String ANNOTATION_SOURCE_LOCATION = "location";
	public static final String ANNOTATION_SCOPE = "scope";
	
	private ITypeBinding scope;
	
	private CompilationUnit compilUnit;
	private ISourceLocation loc;
	
	private final IValueFactory values;
	private final TypeStore typeStore;
	private final BindingConverter bindingConverter;
	private final BindingsImporter bindingsImporter;
	
	public JdtAstToRascalAstConverter(final IValueFactory values, 
									  final TypeStore typeStore, 
									  final BindingConverter bindingConverter,
									  final BindingsImporter bindingsImporter) {
		super(values, typeStore, bindingConverter, bindingsImporter);
		this.values = values;
		this.typeStore = typeStore;
		this.bindingConverter = bindingConverter;
		this.bindingsImporter = bindingsImporter;
	}
	
	public JdtAstToRascalAstConverter getInstance() {
		JdtAstToRascalAstConverter converter = new JdtAstToRascalAstConverter(this.values, this.typeStore, this.bindingConverter, this.bindingsImporter);
		converter.set(compilUnit);
		converter.set(this.loc);
		return converter;
	}
	
	public void set(CompilationUnit compilUnit) {
		this.compilUnit = compilUnit;
	}
	
	public void set(ISourceLocation loc) {
		this.loc = loc;
	}
	
	public void preVisit(ASTNode node) {
		super.preVisit(node);
		scope = this.bindingsImporter.getEnclosingType();
	}
		
	public void postVisit(ASTNode node) {
		super.postVisit(node);
		int start = node.getStartPosition();
		int end = start + node.getLength() - 1;
		setAnnotation(ANNOTATION_SOURCE_LOCATION, values.sourceLocation(loc.getURI(), 
																		start, node.getLength(), 
																		compilUnit.getLineNumber(start), compilUnit.getLineNumber(end), 
																		compilUnit.getColumnNumber(start), compilUnit.getColumnNumber(end)));
		if(scope != null) setAnnotation(ANNOTATION_SCOPE, this.bindingConverter.getEntity(this.scope));
	}
}
