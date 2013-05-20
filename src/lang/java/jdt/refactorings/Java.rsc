@license{
  Copyright (c) 2009-2012 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - A.Izmaylova@cwi.nl}
module lang::java::jdt::refactorings::Java

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::JavaADT;

@doc{Extension of the Rascal 'Id' with enriched type information, used to uniformly represent types and constraint variables}
data Id = method(list[Entity] genericTypes, str name, list[Entity] params, Entity returnType)
        | constr(list[Entity] genericTypes, list[Entity] params)
        
        | field(str name, Entity declaredType)
        | parameter(str name, Entity declaredType)
        | enumConstant(str name, Entity declaredType)
        | variable(str name, Entity declaredType, int id)
        
        | typeParameter(str name, list[Entity] bs) // problematic due to possible cycles
        
        // all the declared types have to be uniquely represented 
        | anonymous(loc location, Entity declaredType) // anonymous declared type, e.g., in the Java 'cast' extressions
        | inherits(Entity declaredType)
        | decl()
        | parameter(int i)
        
        | typeArgument(str name, Entity vc, PEntity pinit)  // value context
		| typeArgument(str name, AstNode tc, PEntity pinit) // term context
		
		| typeArgument(str name, Entity vc, Entity initv)  // value context
		| typeArgument(str name, AstNode tc, Entity initv) // term context
		
		| upper()
		| lower()
		
		| upper(Entity init)
		| lower(Entity init)
		
        ;

public Entity object() = entity([package("java"), package("lang"), class("Object")]);
public Entity zero() = entity([]);

@doc{Declaring type semantics}
public Entity decl(Entity val) = entity(val.id + decl());
@doc{Declared parameter type semantics}
public Entity (Entity) param(int i) = Entity (Entity val) { return entity(val.id + \parameter(i)); };

@doc{Imported compilation unit facts format}
public alias CompilUnit = map[str, rel[Entity, Entity]];
public alias Mapper = map[Entity, tuple[tuple[list[Entity], list[Entity]], Entity]];

@doc{Type values with explicit substitutions of parameterized types}        
data PEntity = pentity(Bindings bindings, Entity genval);
data Bindings = bindings(list[PEntity] args, list[Entity] params);

@doc{Type values with explicit substitutions of parameterized types}        
data PEntity = pentity(Substs s, Entity genval);
data Substs = substs(list[Entity] args, list[Entity] params);

@doc{Annotation that encodes the inversible mapping between the parameterized type representations (with implicit and explicit substitutions)}
anno Entity PEntity@paramval;

public PEntity pentity(Entity genval) = pentity(bindings([],[]), genval)[@paramval=genval];
public PEntity pobject() = pentity(bindings([], []), entity([package("java"), package("lang"), class("Object")]))[@paramval=entity([package("java"), package("lang"), class("Object")])];
public PEntity pzero() = pentity(bindings([], []), entity([]))[@paramval=zero()];
