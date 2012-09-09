@license{
  Copyright (c) 2009-2011 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - ai@cwi.nl}
module lang::java::jdt::refactorings::Java

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::JavaADT;

@doc{Extension of the Rascal Id with enriched type information}
data Id = method(list[Entity] genericTypes, str name, list[Entity] params, Entity returnType)
        | constr(list[Entity] genericTypes, list[Entity] params)
        
        | field(str name, Entity declaredType)
        | parameter(str name, Entity declaredType)
        | enumConstant(str name, Entity declaredType)
        | variable(str name, Entity declaredType, int id)
        
        | typeParameter(str name, list[Entity] bs) // Limitations: cycles in bounds
        
        | anonymous(loc location, Entity declaredType) // represents an anonymous declared type
        | inherits(Entity declaredType) // indicates the declared inherited type
        | decl() // indicates the declaring type of an entity
        | parameter(int i) // indicates the declared parameter type of an entity
        
        // Extension with type argument values that can be associated with two kinds of a context:
        // program element (node) or declaration type value
        | typeArgument(str name, Entity econtext, PEntity init, list[PEntity] bounds)
		| typeArgument(str name, AstNode tcontext, PEntity init, list[PEntity] bounds)
        ;

public Entity object() = entity([package("java"), package("lang"), class("Object")]);
public Entity zero() = entity([]);

@doc{Imported compilation unit facts format}
public alias CompilUnit = map[str, rel[Entity, Entity]];
public alias Mapper = map[Entity, tuple[tuple[list[Entity], list[Entity]], Entity]];

@doc{Type values with explicit substitutions of parameterized types}        
data PEntity = pentity(Bindings bindings, Entity genval);
data Bindings = bindings(list[PEntity] args, list[Entity] params);

public PEntity getGenericVal(PEntity val) = pentity(val.genval)[@paramval=val.genval];
@doc{Annotation that encodes the inversible mapping between the parameterized type representations (with implicit and explicit substitutions)}
anno Entity PEntity@paramval;

public PEntity pentity(Entity genval) = pentity(bindings([],[]), genval)[@paramval=genval];
public PEntity pobject() = pentity(bindings([], []), entity([package("java"), package("lang"), class("Object")]))[@paramval=entity([package("java"), package("lang"), class("Object")])];
public PEntity pzero() = pentity(bindings([], []), entity([]))[@paramval=entity([package("java"), package("lang"), class("Object")])];
