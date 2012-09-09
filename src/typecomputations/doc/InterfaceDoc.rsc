module typecomputations::doc::InterfaceDoc

@doc{Serves as a documentation of the polymorphic interface of type computations}

@doc{Identity monad with the predefined type constructor 'TypeOf' that is required to encapsulate results of all the associated computations}
data TypeOf[&V];

@doc{The inclusion function of an arbitrary monad 
	 that includes the value to an arbitrary defined computation, 
	 where &M stands for a monad specified to be a parameter to the framework}
public &M include(&V val);
@doc{The composition operator of an arbitrary monad}
public &M bind(&M mval, &M (&V) f);
@doc{The extension of an arbitrary monad to a strong arbitrary monad}
public &M bind(&V val1, &M mval2, &M (&V, &V) f);
@doc{Evaluates an arbitrary computation to the result}
public &M1 evalComputation(&M mval);

@doc{The interface used to compute constraint variables and set of constraints for a program element}
public TypeOf[&V] constrainType(&AstNode t);
public set[&Constraint] constrainTypes(&AstNode t);

@doc{The function that lifts a function to produce an arbitrary computation}
public &M (&V) lift(&V1 (&V) f);
@doc{The function that lifts a value to an arbitrary computation of this value}
public &M lift(&V val);

@doc{The function that lifts a function to produce an arbitrary computation}
public &M1 (&V) liftM(&M (&V) f);
@doc{The function that lifts a value to an arbitrary computation of this value}
public &M1 liftM(&M mval);

@doc{The function that allows dispatching to proper computations}
public &MAstNode liftT(AstNode t);
