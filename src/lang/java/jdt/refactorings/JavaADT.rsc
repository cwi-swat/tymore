@license{
  Copyright (c) 2009-2011 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - A.Izmaylova@cwi.nl}
module lang::java::jdt::refactorings::JavaADT

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::Java;

@doc{Type computation model of a compilation unit}
anno map[str, rel[Entity, Entity]] AstNode@typeComputationModel;

@doc{Extension of a type computation model of a compilation unit with the explicit semantics of parameterized types}
anno map[Entity, tuple[tuple[list[Entity], list[Entity]], Entity]] AstNode@semanticsOfParameterizedTypes;

@doc{Certain AstNode are associated with a declaring class scope}
anno Entity AstNode@scope;
