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

public alias ParamSolutions = map[SubstsTL[Entity], SubstsTL_[Entity]];

public set[Constraint[TypeOf[Entity]]] solveit(Constraint::eq(TypeOf[Entity] l, TypeOf[Entity] r));
public set[Constraint[TypeOf[Entity]]] solveit(Constraint::subtype(TypeOf[Entity] l, TypeOf[Entity] r));

public ParamSolutions solutions = ();
public set[Constraint[SubstsT[Entity]]] constraints = {};

@doc{EXTENSION with plain generics}
public set[Constraint[SubstsT[Entity]]] solveit(CompilUnit facts, Mapper mapper, 
												Constraint::eq(SubstsT[Entity] l, SubstsT[Entity] r)) {}
public set[Constraint[SubstsT[Entity]]] solveit(CompilUnit facts, Mapper mapper, 
												Constraint::subtype(SubstsT[Entity] l, SubstsT[Entity] r)) {
	
}

public void intersect(SubstsTL_[Entity] l, SubstsTL_[Entity] r) {
	
}
