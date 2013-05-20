@license{
  Copyright (c) 2009-2011 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - A.Izmaylova@cwi.nl}
module lang::java::jdt::refactorings::JDT4Refactorings

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;
import lang::java::jdt::JDT;

import util::Resources;

@javaClass{prototype.org.rascalmpl.eclipse.library.lang.java.jdt.refactorings.internal.JDT4Refactorings}
@reflect
public java AstNode createAstFromFileR(loc file);

@doc{Creates ASTs from a project}
public set[AstNode] createAstsFromProjectR(loc project) 
	= { createAstFromFileR(f) | /file(loc f) <- getProject(project), f.extension == "java" && isOnBuildPath(f) };