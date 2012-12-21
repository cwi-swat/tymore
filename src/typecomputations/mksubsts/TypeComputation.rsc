module typecomputations::mksubsts::TypeComputation

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;
import lang::java::jdt::refactorings::PrettyPrintUtil;
import lang::java::jdt::refactorings::ValuesUtil;

import typecomputations::mksubsts::BoundSemWithWildCards;
import typecomputations::mksubsts::BoundSemWithoutWildCards;
import typecomputations::mksubsts::LanguageInterface;
import typecomputations::mksubsts::SubstitutionMonad;
import typecomputations::mksubsts::TypeValuesFuncs;

import IO;
import List;
import Map;
import Set;


public SubstsT[Entity] evalc(Entity v) = returnS(eval(v));
public SubstsT[Entity] lookupc(AstNode t) = returnS(lookup(t));

public SubstsT[Entity] gdeclc(Entity v) = returnS(decl(v));
public SubstsT[Entity] (Entity) gparamc(int i) = SubstsT[Entity] (Entity v) { return returnS(param(i)(v)); };

public SubstsT[Entity] gevalcL(Mapper mapper, Entity v)
	= bind(evalc(v), SubstsT[Entity] (Entity vT) { 
			Entity vg = getGenV(mapper, v);
			Entity vgT = eval(vg);
			if(vg == vgT) 
				return returnS(vT); //=> gevalc(v_T) = evalc(v_T);
			return bind(pushSubsts(paramSubstsWith(mapper, vg))(mapper, vgT), SubstsT[Entity] (Entity _) { 
						return returnS(vT); }); });

//public SubstsT[Entity] gevalc(Mapper mapper, Entity v)
//	= bind(evalc(v), SubstsT[Entity] (Entity vT) { 
//			Entity vg = getGenV(mapper, v);
//			Entity vgT = eval(vg);
//			if(vg == vgT) 
//				return returnS(vT); //=> gevalc(v_T) = evalc(v_T);
//			return bind(pushSubsts(paramSubstsWith(mapper, vg))(mapper, vgT), SubstsT[Entity] (Entity _) { 
//						return returnS(vT); }); });

// overrides to account for wildcards
public SubstsT[Entity] gevalc(Mapper mapper, Entity v)
	= bind(evalc(v), SubstsT[Entity] (Entity vT) { 
			Entity vg = getGenV(mapper, v);
			Entity vgT = eval(vg);
			if(vg == vgT) 
				return returnS(vT); //=> gevalc(v_T) = evalc(v_T);
			return bind(pushSubsts(paramSubstsWithCapture(mapper, vg))(mapper, vgT), SubstsT[Entity] (Entity _) { 
						return returnS(boundWcardUB(vT)); }); });


public SubstsT[Entity] glookupc(CompilUnit facts, Mapper mapper, AstNode t)
	= bind(lookupc(t), SubstsT[Entity] (Entity v) { 
			return bind(catchZ(bind(subLookupc(facts, mapper, t), SubstsT[Entity] (Entity vT_) {
									SubstsT[bool] isSup = tauInv(supertypec_(facts, mapper, <vT_, eval(decl(v))>));
									if(tzero() := eval(isSup)) println("<prettyprint(vT_)> --- <prettyprint(eval(decl(v)))> --- <prettyprint(t)>");
									assert(!(tzero() := eval(isSup))); 
									return bind(isSup, SubstsT[Entity] (bool b) {
												assert(b);
												return returnS(zero()); }); }), 
						  	   returnS(zero())), SubstsT[Entity] (Entity _) {
						  	   Substs s = getExprSubsts(mapper, v);
						  	return bind(appnd(paramSubstsWith(mapper, t)(s)), SubstsT[Entity] (value _) {
						  				return returnS(v); }); } ); });

public Substs getExprSubsts(Mapper mapper, Entity v) {
	PEntity pv = mkSubsts(mapper, v);
	if(pv.s == substs([],[])) return pv.s;
	list[Entity] params_ = getGenericTypes(pv.genval);
	if(isEmpty(params_)) return substs([],[]);
	list[Entity] params = pv.s.params;
	list[Entity] args = pv.s.args;
	list[Entity] args_ = [ args[i] | int i <- [0..size(params) - 1], params[i] in params_ ];
	return substs(args_, params_);
}
		
public SubstsT[Entity] subLookupc(CompilUnit facts, Mapper mapper, AstNode t) {
	switch(subterm(t)) {
		case none(): return lift(tzero());
		case some(AstNode t_): return bind(glookupc(facts, mapper, t_), SubstsT[Entity] (Entity v_) { 
										return bind(gevalc(mapper, v_), SubstsT[Entity] (Entity v__) { 
												return bind(boundLkp(facts, mapper, v_), SubstsT[Entity] (Entity _) { 
														return returnS(v__); }); }); });
	};
}

//public SubstsT[Entity] boundLkp(CompilUnit facts, Mapper mapper, Entity v) {
//	Entity vT = eval(getGenV(mapper, v)); // tracer(true, "boundLkp: <prettyprint(vT)>; <prettyprint(v)>");
//	return catchZ(boundS(mapper, vT), boundEnv(facts, mapper, vT));
//}

// overrides to account for wildcards
public SubstsT[Entity] boundLkp(CompilUnit facts, Mapper mapper, Entity v) {
	Entity vT = eval(getGenV(mapper, v)); // tracer(true, "boundLkp: <prettyprint(vT)>; <prettyprint(v)>");
	return catchZ(boundSu(mapper, vT), boundEnv(facts, mapper, vT));
}

public SubstsT_[bool] supertypec_(CompilUnit facts, Mapper mapper, tuple[Entity, Entity] ts) {
	if(ts[0] == object()) return returnS_(ts[0] == ts[1] ? true : false);
	if(isSub(mapper, ts[0],ts[1])) return returnS_(true);
	return bind(lift(supertypes(facts, ts[0])), SubstsT_[bool] (Entity vS1) { 
			return bind(supertypec_(facts, mapper, <vS1, ts[1]>), SubstsT_[bool] (bool b) {
						if(!b) return lift([]);
						return bind(lift(supertypes(facts, getGenV(mapper, ts[0]))), SubstsT_[bool] (Entity vS2) { 
									if(getGenV(mapper, vS1) != getGenV(mapper, vS2)) return lift([]);
									return bind(tau(pushSubsts(paramSubstsWith(mapper, inherits(getGenV(mapper, ts[0]), vS2)))(mapper, vS2)), SubstsT_[bool] (Entity _) { 
												return returnS_(b); }); }); }); });
}
public bool isSub(Mapper mapper, Entity sub, Entity sup) = (mkSubsts(mapper, sub).genval == mkSubsts(mapper, sup).genval);

@doc{A function that returns the lookup subterm}
public Option[AstNode] subterm(e:classInstanceCreation(none(),_,[],_,none())) = none();
public Option[AstNode] subterm(e:classInstanceCreation(some(AstNode expr),_,[],_,none())) = some(rmv(expr));
public Option[AstNode] subterm(e:classInstanceCreation(_,_,[],_,some(AstNode anonymClass))) = none(); 
public Option[AstNode] subterm(e:fieldAccess(AstNode expr,_)) = some(rmv(expr)); 
public Option[AstNode] subterm(e:methodInvocation(none(),_,_,_)) = some(thisExpression(none())[@bindings = ("typeBinding" : e@scope)]);
public Option[AstNode] subterm(e:methodInvocation(some(AstNode expr),_,_,_)) = some(rmv(expr));
public Option[AstNode] subterm(e:qualifiedName(AstNode qname,_)) = (isVariableBinding(lookup(e))) ? some(qname) : none(); 
public Option[AstNode] subterm(e:simpleName(_)) = (isFieldBinding(lookup(e)) && !isArrayType(getType(e))) ? some(thisExpression(none())[@bindings = ("typeBinding" : e@scope)]) : none();
public Option[AstNode] subterm(e:superConstructorInvocation(none(),_,_)) = some(thisExpression(none())[@bindings = ("typeBinding" : e@scope)]);
public Option[AstNode] subterm(e:superConstructorInvocation(some(AstNode expr),_,_)) = some(rmv(expr));
public Option[AstNode] subterm(e:superFieldAccess(none(),_)) = some(thisExpression(none())[@bindings = ("typeBinding" : e@scope)]);
public Option[AstNode] subterm(e:superFieldAccess(some(AstNode qualifier),_)) = some(qualifier); 
public Option[AstNode] subterm(e:superMethodInvocation(none(),_,_,_)) = some(thisExpression(none())[@bindings = ("typeBinding" : e@scope)]);
public Option[AstNode] subterm(e:superMethodInvocation(some(AstNode qualifier),_,_,_)) = some(qualifier); 
public default Option[AstNode] subterm(AstNode t) = none();

public AstNode rmv(parenthesizedExpression(AstNode expr)) = rmv(expr);
public default AstNode rmv(AstNode expr) = expr;

