@license{
  Copyright (c) 2009-2011 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - A.Izmaylova@cwi.nl}
module prototype::computations::mksubsts::AbstractConstraintSolver

import prototype::computations::mksubsts::ConstraintInference;


public data Entity = sub(Entity entity);

public alias Solutions = map[Entity, Entity];
public alias GensSolutions = map[SubstsTL[Entity], SubstsTL[Entity]];

public set[Constraint[TypeOf[Entity]]] solveit(Constraint::eq(TypeOf[Entity] l, TypeOf[Entity] r));
public set[Constraint[TypeOf[Entity]]] solveit(Constraint::subtype(TypeOf[Entity] l, TypeOf[Entity] r));

/*
- refactoring - semantics-preserving - non-arbitrary init solution space (subtypes or supertypes of initial)
- allow a conditional inference in presence of parameterized (constraint variables) substitution: intersection
- substitution gets a condition
- each constraint variable - is a set of possible solutions
- each constraint shrinks the set of possible solutions of two constraint variables
- each generic solution can potentially require extra constraints on type arguments (intersection under type argument constraints),
- getting supertypes can introduce a constraint variable
*/

@doc{EXTENSION with plain generics}
public set[Constraint[SubstsT[Entity]]] solveit(CompilUnit facts, Mapper mapper, 
												Constraint::eq(SubstsT[Entity] l, SubstsT[Entity] r)) {}
public set[Constraint[SubstsT[Entity]]] solveit(CompilUnit facts, Mapper mapper, 
												Constraint::subtype(SubstsT[Entity] l, SubstsT[Entity] r)) {
	// initialize first...
	solutions[l] = solutions[l] ? gevalc(l);
	solutions[r] = solutions[r] ? gevalc(r);
	// 
	
}

public void intersect(Constraint::subtype(SubstsT[Entity] l, SubstsT[Entity] r)) {
	bind(tau(l), SubstsT_[Entity] (Entity lv) { 
		return bind(supertypes_(facts, mapper, lv), SubstsT_[Entity] (Entity sup) { 
					return bind(lift(r), SubstsT_[Entity] (Entity rv) {
								return if(sup == rv) returnS_(rv); else lift([]); }); }); });
}

public void sups();
public void subs();