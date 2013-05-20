@license{
  Copyright (c) 2009-2011 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - A.Izmaylova@cwi.nl}
module prototype::lang::java::jdt::refactorings::JavaADT

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import prototype::lang::java::jdt::refactorings::Java;

@doc{Type computation model of a compilation unit}
anno map[str, rel[Entity, Entity]] AstNode@typeComputationModel;

public alias TArgsToTParams = tuple[list[Entity] targs, list[Entity] tparams];
public alias Substitutions = tuple[TArgsToTParams substs, Entity val];
public alias Mapper = map[Entity val, Substitutions substs];

@doc{Extension of a type computation model of a compilation unit with the explicit semantics of parameterized types}
anno Mapper AstNode@semanticsOfParameterizedTypes;

@doc{Certain AstNode are associated with a declaring class scope}
anno list[Entity] AstNode@scopes;
