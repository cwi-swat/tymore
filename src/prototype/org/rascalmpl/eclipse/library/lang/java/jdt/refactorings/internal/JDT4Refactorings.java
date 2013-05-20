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

import org.eclipse.core.resources.IFile;
import org.eclipse.imp.pdb.facts.IConstructor;
import org.eclipse.imp.pdb.facts.ISourceLocation;
import org.eclipse.imp.pdb.facts.IValue;
import org.eclipse.imp.pdb.facts.IValueFactory;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.compiler.IProblem;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.rascalmpl.eclipse.library.lang.java.jdt.internal.JDT;
import org.rascalmpl.interpreter.IEvaluatorContext;
import org.rascalmpl.interpreter.control_exceptions.Throw;

public class JDT4Refactorings {
	
	private final IValueFactory values;
	
	private JdtAstToRascalAstConverter converter;
	
	public JDT4Refactorings(IValueFactory values) {
    	this.values = values;
	}
	
	public IValue createAstFromFileR(ISourceLocation loc, IEvaluatorContext eval) {
		CompilationUnit cu = this.getCompilationUnit(loc);
		BindingConverter bindingConverter = new BindingConverter();
		converter = new JdtAstToRascalAstConverter(values, 
												   eval.getHeap().getModule("prototype::lang::java::jdt::refactorings::JDT4Refactorings").getStore(), 
												   bindingConverter);
		converter.set(cu);
		converter.set(loc);
		cu.accept(converter);
		IValue compilUnitValue = converter.getValue();
		
		TypeComputationModelBuilder typeComputationModelBuilder = new TypeComputationModelBuilder(values, new BindingConverter());
		typeComputationModelBuilder.extract(this.getCompilationUnit(loc));
		
		compilUnitValue = ((IConstructor) compilUnitValue).setAnnotation("typeComputationModel", typeComputationModelBuilder.getTypeComputationModel());
		compilUnitValue = ((IConstructor) compilUnitValue).setAnnotation("semanticsOfParameterizedTypes", typeComputationModelBuilder.getSemanticsOfParameterizedTypes());
		return compilUnitValue;
	}
	
	@SuppressWarnings({ "deprecation"})
	public CompilationUnit getCompilationUnit(ISourceLocation loc) {	
		IFile file = new JDT(values).getJavaIFileForLocation(loc);	
		ICompilationUnit icu = JavaCore.createCompilationUnitFrom(file);
		ASTParser parser = ASTParser.newParser(AST.JLS3);
		parser.setResolveBindings(true);
		parser.setSource(icu);
		CompilationUnit cu = (CompilationUnit) parser.createAST(null);
		int i;
		IProblem[] problems = cu.getProblems();
		for (i = 0; i < problems.length; i++) {
			if (problems[i].isError()) {
				int offset = problems[i].getSourceStart();
				int length = problems[i].getSourceEnd() - offset;
				int sl = problems[i].getSourceLineNumber();
				ISourceLocation pos = values.sourceLocation(loc.getURI(), offset, length, sl, sl, 0, 0);
				throw new Throw(values.string("Error(s) in compilation unit: " + problems[i].getMessage()), pos, null);
			}
		}
		return cu;
	}
}