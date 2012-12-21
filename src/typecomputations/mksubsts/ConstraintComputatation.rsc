module typecomputations::mksubsts::ConstraintComputatation

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;
import lang::java::jdt::refactorings::JavaADTVisitor;
import lang::java::jdt::refactorings::PrettyPrintUtil;
import lang::java::jdt::refactorings::ValuesUtil;

import typecomputations::mksubsts::BoundSemWithoutWildCards;
import typecomputations::mksubsts::BoundSemWithWildCards;
import typecomputations::mksubsts::LanguageInterface;
import typecomputations::mksubsts::SubstitutionMonad;
import typecomputations::mksubsts::TypeComputation;
import typecomputations::mksubsts::TypeValuesFuncs;

import Prelude;

public data Constraint[&M] = eq(&M lh, &M rh)
					  		 | subtype(&M lh, &M rh)
					  		 ;
					  		 
public set[Constraint[SubstsT[Entity]]] constrain(t:arrayAccess(_,_), CompilUnit facts, Mapper mapper) 
	= {};	
public set[Constraint[SubstsT[Entity]]] constrain(t:arrayCreation(_, list[AstNode] _, some(AstNode initializer)), CompilUnit facts, Mapper mapper) 
	= { subtype(glookupc(facts, mapper, rmv(initializer)), glookupc(facts, mapper, t)) }
	;	
public set[Constraint[SubstsT[Entity]]] constrain(t:arrayInitializer(list[AstNode] exprs), CompilUnit facts, Mapper mapper) 
	= { subtype(glookupc(facts, mapper, rmv(expr)), glookupc(facts, mapper, t)) | expr <- exprs }
	;	
public set[Constraint[SubstsT[Entity]]] constrain(t:assignment(AstNode _, nullLiteral()), CompilUnit facts, Mapper mapper) 
	= {};
public set[Constraint[SubstsT[Entity]]] constrain(t:assignment(AstNode lt, AstNode rt), CompilUnit facts, Mapper mapper) 
	= { subtype(glookupc(facts, mapper, rmv(rt)), glookupc(facts, mapper, rmv(lt))) }
	;
public set[Constraint[SubstsT[Entity]]] constrain(t:castExpression(_, AstNode e), CompilUnit facts, Mapper mapper) 
	= { (isDownCast(facts, mapper, t)) ? subtype(glookupc(facts, mapper, t), glookupc(facts, mapper, rmv(e))) 
									   : subtype(glookupc(facts, mapper, rmv(e)), glookupc(facts, mapper, t)) }
	;
public set[Constraint[SubstsT[Entity]]] constrain(t:classInstanceCreation(none(),_, [], [],_), CompilUnit facts, Mapper mapper) 
	= {};
public set[Constraint[SubstsT[Entity]]] constrain(t:classInstanceCreation(none(),_, [], list[AstNode] args,_), CompilUnit facts, Mapper mapper) 
	= { subtype(glookupc(facts, mapper, rmv(args[i])), bind(glookupc(facts, mapper, t), gparamc(i))) | int i <- [0..size(args) - 1], args[i] != nullLiteral() }
	;
public set[Constraint[SubstsT[Entity]]] constrain(t:classInstanceCreation(some(AstNode e),_, [], list[AstNode] args, none()), CompilUnit facts, Mapper mapper) {
	if(isEmpty(args)) return {};
	return  { subtype(glookupc(facts, mapper, rmv(args[i])), bind(glookupc(facts, mapper, t), gparamc(i))) | int i <- [0..size(args) - 1], args[i] != nullLiteral() } 
		  + { subtype(glookupc(facts, mapper, rmv(e)), bind(glookupc(facts, mapper, t), gdeclc)) };
}	
public set[Constraint[SubstsT[Entity]]] constrain(t:classInstanceCreation(_,_, [], list[AstNode] args, some(AstNode anonym)), CompilUnit facts, Mapper mapper) 
	= {};
public set[Constraint[SubstsT[Entity]]] constrain(t:conditionalExpression(AstNode _, AstNode thenBranch, AstNode elseBranch), CompilUnit facts, Mapper mapper) 
	=   { subtype(glookupc(facts, mapper, t), glookupc(facts, mapper, rmv(thenBranch))) }
	  + { subtype(glookupc(facts, mapper, t), glookupc(facts, mapper, rmv(elseBranch))) }
	;
public set[Constraint[SubstsT[Entity]]] constrain(t:constructorInvocation(_, list[AstNode] args), CompilUnit facts, Mapper mapper) {
	if(isEmpty(args)) return {};
	return { subtype(glookupc(facts, mapper, rmv(args[i])), bind(glookupc(facts, mapper, t), gparamc(i))) | int i <- [0..size(args) - 1], args[i] != nullLiteral() };
}
public set[Constraint[SubstsT[Entity]]] constrain(t:fieldAccess(AstNode e,_), CompilUnit facts, Mapper mapper) 
	= { eq(glookupc(facts, mapper, rmv(e)), bind(glookupc(facts, mapper, t), gdeclc)) }
	;
public set[Constraint[SubstsT[Entity]]] constrain(t:methodInvocation(none(),_,_, list[AstNode] args), CompilUnit facts, Mapper mapper) {
	if(isEmpty(args)) return {};
	return { subtype(glookupc(facts, mapper, rmv(args[i])), bind(glookupc(facts, mapper, t), gparamc(i))) | int i <- [0..size(args) - 1], args[i] != nullLiteral() };
}
public set[Constraint[SubstsT[Entity]]] constrain(t:methodInvocation(some(AstNode e),_,_, list[AstNode] args), CompilUnit facts, Mapper mapper) { 
	set[Constraint[SubstsT[Entity]]] cons = { subtype(glookupc(facts, mapper, rmv(e)), bind(glookupc(facts, mapper, t), gdeclc)) };
	if(isEmpty(args)) return cons; 
	set[Constraint[SubstsT[Entity]]] cons_ = { subtype(glookupc(facts, mapper, rmv(args[i])), bind(glookupc(facts, mapper, t), gparamc(i))) | int i <- [0..size(args) - 1], args[i] != nullLiteral() };
	return cons + cons_;
}
public set[Constraint[SubstsT[Entity]]] constrain(t:qualifiedName(_,_), CompilUnit facts, Mapper mapper) 
	= {};
public set[Constraint[SubstsT[Entity]]] constrain(t:superConstructorInvocation(some(AstNode e), _, list[AstNode] args), CompilUnit facts, Mapper mapper) {
	set[Constraint[SubstsT[Entity]]] cons = { subtype(glookupc(facts, mapper, rmv(e)), bind(glookupc(facts, mapper, t), gdeclc)) };
	if(isEmpty(args)) return cons;
	set[Constraint[SubstsT[Entity]]] cons_ = { subtype(glookupc(facts, mapper, rmv(args[i])), bind(lookup(facts, mapper, t), gparamc(i))) | int i <- [0..size(args) - 1], args[i] != nullLiteral() };
	return cons + cons_;
}
public set[Constraint[SubstsT[Entity]]] constrain(t:superFieldAccess(_,_), CompilUnit facts, Mapper mapper) 
	= {};
public set[Constraint[SubstsT[Entity]]] constrain(t:superMethodInvocation(_,_,_, list[AstNode] args), CompilUnit facts, Mapper mapper) {
	if(isEmpty(args)) return {};
	return { subtype(glookupc(facts, mapper, rmv(args[i])), bind(glookupc(facts, mapper, t), gparamc(i))) | int i <- [0..size(args) - 1], args[i] != nullLiteral() };
}
public set[Constraint[SubstsT[Entity]]] constrain(t:singleVariableDeclaration(str name,_,_, some(nullLiteral()),_), CompilUnit facts, Mapper mapper) 
	= {};
public set[Constraint[SubstsT[Entity]]] constrain(t:singleVariableDeclaration(str name,_,_, some(AstNode initializer),_), CompilUnit facts, Mapper mapper) 
	= { subtype(glookupc(facts, mapper, rmv(initializer)), glookupc(facts, mapper, setAnnotations(simpleName(name), getAnnotations(t)))) }
	;
public set[Constraint[SubstsT[Entity]]] constrain(t:variableDeclarationFragment(str name, some(nullLiteral())), CompilUnit facts, Mapper mapper) 
	= {};
public set[Constraint[SubstsT[Entity]]] constrain(t:variableDeclarationFragment(str name, some(AstNode initializer)), CompilUnit facts, Mapper mapper) 
	= { subtype(glookupc(facts, mapper, rmv(initializer)), glookupc(facts, mapper, setAnnotations(simpleName(name), getAnnotations(t)))) }
	;
public default set[Constraint[SubstsT[Entity]]] constrain(AstNode t, CompilUnit facts, Mapper mapper) = {};

public bool isDownCast(CompilUnit facts, Mapper mapper, t:castExpression(_, AstNode e)) {
	TypeOf[bool] b = eval(tauInv(supertypec_(facts, mapper, <getType(t), getType(e)>)));
	if(tzero() := b) return false;
	return true;
}


// Ensuring 'Invariance'

public Constraint[SubstsT[&T1]] (Constraint[SubstsT[&T]]) apply(SubstsT[&T1] (&T) f) 
	= Constraint[SubstsT[&T1]] (Constraint[SubstsT[&T]] c) {
			switch(c) {
				case subtype(SubstsT[&T] lh, SubstsT[&T] rh): return subtype(bind(lh, f), bind(rh, f));
				case eq(SubstsT[&T] lh, SubstsT[&T] rh): return eq(bind(lh, f), bind(rh, f));
			}
	  }; 
	  
public Constraint[SubstsT[&T1]] (Constraint[SubstsT[&T]]) apply(SubstsT[&T1] (&T) f1, SubstsT[&T1] (&T) f2) 
	= Constraint[SubstsT[&T1]] (Constraint[SubstsT[&T]] c) {
			switch(c) {
				case subtype(SubstsT[&T] lh, SubstsT[&T] rh): return subtype(bind(lh, f1), bind(rh, f2));
				case eq(SubstsT[&T] lh, SubstsT[&T] rh): return eq(bind(lh, f1), bind(rh, f2));
			}
	  }; 

	  
public set[Constraint[SubstsT[&T]]] catchZ(CompilUnit facts, Mapper mapper, Constraint[SubstsT[&T]] c) {
	switch(c) {
		case subtype(lh, rh): {
			TypeOf[tuple[&T, Substs]] lh_ = run(lh)(substs([],[]));
			if(tzero() := lh_) return {};
			TypeOf[tuple[&T, Substs]] rh_ = run(rh)(substs([],[]));
			if(tzero() := rh_) return {};
			return { subtype(substs( TypeOf[tuple[&T, Substs]] (Substs s) { return lh_; } ), 
							 substs( TypeOf[tuple[&T, Substs]] (Substs s) { return rh_; } )) };
		}
		case eq(lh, rh): { 			
			TypeOf[tuple[&T, Substs]] lh_ = run(lh)(substs([],[]));
			if(tzero() := lh_) return {};
			TypeOf[tuple[&T, Substs]] rh_ = run(rh)(substs([],[]));
			if(tzero() := rh_) return {};
			return { eq(substs( TypeOf[tuple[&T, Substs]] (Substs s) { return lh_; } ), 
						substs( TypeOf[tuple[&T, Substs]] (Substs s) { return rh_; } )) };
		}
	}
}
	  
//public set[Constraint[SubstsT[Entity]]] gevalc(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
//	= { apply(SubstsT[Entity] (Entity v) { 
//				return bind(gevalc(mapper, v), SubstsT[Entity] (Entity v_) {
//								return boundS(mapper, eval(getGenV(mapper, v))); }); })(c) }; 

// overrides to account for wildcards
public set[Constraint[SubstsT[Entity]]] gevalc(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return bind(gevalcL(mapper, v), SubstsT[Entity] (Entity v_) {
								return boundSu(mapper, eval(getGenV(mapper, v))); }); },
			  SubstsT[Entity] (Entity v) { 
				return bind(gevalc(mapper, v), SubstsT[Entity] (Entity v_) {
								return boundSl(mapper, eval(getGenV(mapper, v))); }); })(c) }; 

public set[Constraint[SubstsT[Entity]]] boundS_(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return boundS_(mapper, v); })(c) }; 

public set[Constraint[SubstsT[Entity]]] boundS(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return boundS(mapper, v); })(c) }; 

// extends to account for wildcards
public set[Constraint[SubstsT[Entity]]] boundSu_(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return boundSu_(mapper, v); })(c) }; 
// extends to account for wildcards
public set[Constraint[SubstsT[Entity]]] boundSu(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return boundSu(mapper, v); })(c) }; 
// extends to account for wildcards
public set[Constraint[SubstsT[Entity]]] boundSl_(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return boundSl_(mapper, v); })(c) };
// extends to account for wildcards 
public set[Constraint[SubstsT[Entity]]] boundSl(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) 
	= { apply(SubstsT[Entity] (Entity v) { 
				return boundSl(mapper, v); })(c) }; 

				
public set[Constraint[SubstsT[Entity]]] supertypec(CompilUnit facts, Mapper mapper, Constraint::subtype(SubstsT[Entity] lh, SubstsT[Entity] rh))
	= { subtype(bind(discard(rh), SubstsT[Entity] (Entity v2) { 
						return bind(lh, SubstsT[Entity] (Entity v1) {
								SubstsT[bool] isSup = tauInv(supertypec_(facts, mapper, <v1, v2>)); assert(!(tzero() := eval(isSup)));
								return bind(isSup, SubstsT[Entity] (bool b) { assert(b);
									return returnS(v2); }); }); }),
					 rh) };

public set[Constraint[SubstsT[Entity]]] supertypec(CompilUnit facts, Mapper mapper, c:Constraint::eq(SubstsT[Entity] lh, SubstsT[Entity] rh)) = { c };

public set[Constraint[SubstsT[Entity]]] inferTAs(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c)
	= { * ( subtyping(facts, mapper, c__) + { c__ } ) | Constraint[SubstsT[Entity]] c_  <- gevalc(facts, mapper, c),
										                Constraint[SubstsT[Entity]] c__ <- catchZ(facts, mapper, c_) };

public set[Constraint[SubstsT[Entity]]] subtyping(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	return { c3_ | Constraint[SubstsT[Entity]] c1  <- boundS(facts, mapper, c), 
				   Constraint[SubstsT[Entity]] c1_ <- catchZ(facts, mapper, c1),
				   Constraint[SubstsT[Entity]] c2  <- supertypec(facts, mapper, c1_),
				   Constraint[SubstsT[Entity]] c2_ <- catchZ(facts, mapper, c2), 
				   Constraint[SubstsT[Entity]] c3  <- invariant(facts, mapper, c2_),
				   Constraint[SubstsT[Entity]] c3_ <- catchZ(facts, mapper, c3) };
}

//public set[Constraint[SubstsT[Entity]]] invariant(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
//	TypeOf[Entity] rh_ = eval(c.rh);
//	if(tzero() := rh_) return {};
//	Entity rhv = rh_.v;
//	return { *( subtyping(facts, mapper, c___) + { c___ } ) 
//						| Entity param <- getTypeParamsOrArgs(getGenV(mapper, rhv)), 
//						  Constraint[SubstsT[Entity]] c_ := apply(SubstsT[Entity] (Entity _) { return returnS(param); })(c),
//						  Constraint[SubstsT[Entity]] c__  <- boundS_(facts, mapper, eq(c_.lh, c_.rh)),
//						  Constraint[SubstsT[Entity]] c___ <- catchZ(facts, mapper, c__) };
//}

// overrides to account for wildcards
public set[Constraint[SubstsT[Entity]]] invariant(CompilUnit facts, Mapper mapper, Constraint[SubstsT[Entity]] c) {
	TypeOf[Entity] rh_ = eval(c.rh);
	if(tzero() := rh_) return {};
	Entity rhv = rh_.v;
	return { *( subtyping(facts, mapper, c___l)  + subtyping(facts, mapper, c___u) + { c___ } + { c___l } + { c___u } ) 
						| Entity param <- getTypeParamsOrArgs(getGenV(mapper, rhv)), 
						  Constraint[SubstsT[Entity]] c_ := apply(SubstsT[Entity] (Entity _) { return returnS(param); })(c),
						  Constraint[SubstsT[Entity]] c__  <- boundS_(facts, mapper, eq(c_.lh, c_.rh)),
						  Constraint[SubstsT[Entity]] c___ <- catchZ(facts, mapper, c__),
						  
						  Constraint[SubstsT[Entity]] c__u  <- boundSu_(facts, mapper, subtype(c_.lh, c_.rh)),
						  Constraint[SubstsT[Entity]] c___u <- catchZ(facts, mapper, c__u),
						  
						  Constraint[SubstsT[Entity]] c__l  <- boundSl_(facts, mapper, subtype(c_.rh, c_.lh)),
						  Constraint[SubstsT[Entity]] c___l <- catchZ(facts, mapper, c__l) };
}

//=================================================================================================

public str prettyprint(Constraint::eq(SubstsT[Entity] lh, SubstsT[Entity] rh)) = "<prettyprint(eval(lh))> == <prettyprint(eval(rh))>"; 
public str prettyprint(Constraint::subtype(SubstsT[Entity] lh, SubstsT[Entity] rh)) = "<prettyprint(eval(lh))> \<: <prettyprint(eval(rh))>"; 

public str prettyprint(Constraint::eq(&M lh, &M rh)) = "<prettyprint(lh)> == <prettyprint(rh)>"; 
public str prettyprint(Constraint::subtype(&M lh, &M rh)) = "<prettyprint(lh)> \<: <prettyprint(rh)>"; 

