@license{
  Copyright (c) 2009-2011 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - A.Izmaylova@cwi.nl}
module lang::java::jdt::refactorings::Java

import lang::java::jdt::Java;

@doc{Extension of the Rascal Id with enriched type information}
data Id = method(list[Entity] genericTypes, str name, list[Entity] params, Entity returnType)
        | constr(list[Entity] genericTypes, list[Entity] params)
        
        | field(str name, Entity declaredType)
        | parameter(str name, Entity declaredType)
        | enumConstant(str name, Entity declaredType)
        | variable(str name, Entity declaredType, int id)
        
        | typeParameter(str name, list[Entity] bounds)
        
        | anonymous(loc location, Entity declaredType) // represents an anonymous declared type
        | inherits(Entity declaredType) // indicates the declared inherited type
        | decl() // indicates the declaring type
        | parameter(int i) // indicates the declared parameter type
        ;
