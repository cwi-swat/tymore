@license{
  Copyright (c) 2009-2012 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - A.Izmaylova@cwi.nl}
module prototype::lang::java::jdt::refactorings::Java

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import prototype::lang::java::jdt::refactorings::JavaADT;

@doc{Extension of the Rascal 'Id' with enriched type information, used to uniformly represent types and constraint variables}
data Id = method(list[Entity] genericTypes, str name, list[Entity] params, Entity returnType)
        | constr(list[Entity] genericTypes, list[Entity] params)  
        | field(str name, Entity declaredType)
        | parameter(str name, Entity declaredType)
        | enumConstant(str name, Entity declaredType)
        | variable(str name, Entity declaredType, int id)
        
        // all the declared types have to be uniquely represented,
        // 		e.g., anonymous declared types in the Java 'cast' extressions 
        | anonymous(loc location, Entity declaredType)
        | inherits(Entity declaredType)
        | decl()
        | parameter(int i)
        
		| typeArgument(str name, Entity valuec, Entity init) // value context
		| typeArgument(str name, AstNode termc, Entity init) // term context
		
		| upper(Entity init)
		| lower(Entity init)
        ;

public Entity object() = entity([package("java"), package("lang"), class("Object")]);
public Entity zero() = entity([]);

@doc{Imported compilation unit facts format}
public alias CompilUnit = map[str, rel[Entity, Entity]];
public alias Mapper = map[Entity, tuple[tuple[list[Entity], list[Entity]], Entity]];

@doc{Type values with explicit substitutions of parameterized types}        
data PEntity = pentity(Substs s, Entity genval);
data Substs = substs(list[Entity] args, list[Entity] params);

@doc{Annotation that encodes the inversible mapping between the parameterized type representations with implicit and explicit substitutions}
anno Entity PEntity@paramval;
