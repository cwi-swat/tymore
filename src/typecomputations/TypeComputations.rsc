@doc{Monadic based type computations}
module typecomputations::TypeComputations

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;
import lang::java::jdt::refactorings::PrettyPrintUtil;

import typecomputations::SemanticDomains;
import typecomputations::TypeMonadTransformers;
import typecomputations::TypeValues;
import typecomputations::TypeValuesPlusGens;

import Prelude;


@doc{The framework lifting mechanism :
	 parameters: M       - type constructor of a monad
	 			 inclM - inclusion function of a monad
	 			 bind    - composition operator of a monad
	 			 run     - execution function
	 			 liftM   - 'monad-to-monad' morphisms}

public M[&F1] bindinj(M[&F] mval, M[&F1] (TVal[&F]) f) 
	= bind(mval, M[&F1] (&F val) { return bind(f(inj(val)), M[&F1] (&F1 v) { return liftM(prjAll(v)); }); })
	;
public M[&F3] bindinj(M[&F1] mval1, M[&F2] mval2, M[&F3] (TVal[&F1], TVal[&F2]) f) 
	= bind(mval1, M[&F3] (&F1 val1) { return bind(mval2, M[&F3] (&F2 val2) { return bind(f(inj(val1), inj(val2)), M[&F3] (&F3 val3) { return liftM(prjAll(val3)); }); }); } )
	;
//===========================================================
public M[Entity] clookup(wrapval(AstNode t)) { tracer(false, "lookup 1st level: <prettyprint(t)>"); return liftM(lookup(t)); }
public M[Entity] ceval(wrapval(Entity val)) { tracer(false, "eval 1st level: <prettyprint(val)>"); return liftM(eval(val)); }
public M[Entity] (Entity) cparam(wrapval(int i)) = M[Entity] (Entity val) { return liftM(param(val, i)); };
public M[Entity] cdecl(wrapval(Entity val)) = liftM(decl(val));
//=============== tracable ==================================
public M[Entity] clookup(nestval(wrapval(AstNode t))) 
	{ println("lookup 2nd level: <prettyprint(t)>"); 
	  return bind( liftM(bind(assignSTerm(t), StateTypeOf[AstNode] (AstNode _) { return fetchSTerm(); } )), M[Entity] (AstNode tt) { return clookup(inj1(tt)); } )
	;}
//=============== explicit substitutions ====================
public M[PEntity] cmkSubstsExplicit(wrapval(Entity val)) 
	= bind(liftM(fetchMMapper()), M[PEntity] (Mapper mapper) { return liftM(mkSubstsExplicit(mapper, val)); })
	;
public M[PEntity] (TVal[PEntity]) mkSubstsExplicitTr1(M[Entity] (TVal[Entity]) f) 
	= M[PEntity] (TVal[PEntity] val) { return bindinj(bindinj(liftM(prjAll(val)@paramval), f), cmkSubstsExplicit); }
	;
public M[PEntity] (TVal[AstNode]) mkSubstsExplicitTr2(M[Entity] (TVal[AstNode]) f)
	= M[PEntity] (TVal[AstNode] t) { return bindinj(bindinj(liftM(prjAll(t)), f), cmkSubstsExplicit); }
	;
public M[PEntity] geval(wrapval(PEntity val))
	= bindinj(liftM(val), mkSubstsExplicitTr1(ceval))
	;
public M[PEntity] glookup(wrapval(AstNode t))
	= bindinj(liftM(t), mkSubstsExplicitTr2(M[Entity] (TVal[AstNode] tt) { return clookup(tt); }))
	;
public M[PEntity] (PEntity) gparam(wrapval(int i)) 
	= M[PEntity] (PEntity val) { return liftM(param(val, i)); }
	; 
public M[PEntity] gdecl(wrapval(PEntity val)) = liftM(decl(val)); 
//=============== parameterization ==========================
public Option[AstNode] getScopeTerm(AstNode t) = subterm(t);

public M[PEntity] geval(nestval(wrapval(PEntity val))) 
	= bindinj(liftM(val), bind(liftM(getGenericVal(val)), M[PEntity] (PEntity v) { return geval(inj1(v)); }), parameterize11 )
	;
//public M[PEntity] glookup(nestval(wrapval(AstNode t))) 
//	= (some(AstNode st) := getScopeTerm(t)) 
//		? bindinj( o( bindinj(bindinj(bindinj(liftM(st), glookup), filt2), geval), liftM(fetchv) ),
//			       bindinj( bind(liftM(t), M[PEntity] (AstNode tt) { return glookup(inj1(tt)); }), filt1),
//			       parameterize21
//		         )
//		: bindinj( bindinj( bind(liftM(t), M[PEntity] (AstNode tt) { return glookup(inj1(tt)); }), filt1),
//			       parameterize22
//		         )
//	;
public M[PEntity] (PEntity) gparam(nestval(wrapval(int i))) 
	= M[PEntity] (PEntity val) { return bindinj(gparam(inj1(i))(val), filt3); }
	; 
public M[PEntity] gdecl(nestval(wrapval(PEntity val))) { tracer(false, "gdecl 2nd level : "); return bindinj(gdecl(inj1(val)), filt3); }
public M[PEntity] filt1(wrapval(PEntity val)) = filt(bool (PEntity v) { return false; }, inj(val));
public M[PEntity] filt2(wrapval(PEntity val)) = filt(bool (PEntity v) { return false; }, inj(val));
public M[PEntity] filt3(wrapval(PEntity val)) = filt(bool (PEntity v) { return true; }, inj(val));
public M[PEntity] filt(bool (PEntity) p, wrapval(PEntity val)) 
	= p(val) ? bind(geval(inj(val)), M[PEntity] (PEntity v) { return liftM(toConst(v)); }) : liftM(val)
	;
public M[PEntity] parameterize11(wrapval(PEntity val1), wrapval(PEntity val2)) 
	= bind(liftM(fetchSTerm()), M[PEntity] (AstNode t) { 
		return bind(liftM(fetchMFacts()), M[PEntity] (CompilUnit facts) { 
			return bind(liftM(fetchMMapper()), M[PEntity] (Mapper mapper) { 
				return liftM(parameterize1(facts, mapper, t, val1, val2)); }); }); })
	;
public M[PEntity] parameterize21(wrapval(PEntity val1), wrapval(PEntity val2)) 
	= bind(liftM(fetchSTerm()), M[PEntity] (AstNode t) { 
		return bind(liftM(fetchMFacts()), M[PEntity] (CompilUnit facts) { 
			return bind(liftM(fetchMMapper()), M[PEntity] (Mapper mapper) { 
				return liftM(parameterize2(facts, mapper, t, val1, val2)); }); }); })
	;
public M[PEntity] parameterize22(wrapval(PEntity val)) 
	= bind(liftM(fetchSTerm()), M[PEntity] (AstNode t) { 
		return bind(liftM(fetchMFacts()), M[PEntity] (CompilUnit facts) { 
			return bind(liftM(fetchMMapper()), M[PEntity] (Mapper mapper) { 
				return liftM(parameterize2(facts, mapper, t, val)); }); }); })
	;

public default M[Entity] ceval(TVal[Entity] val) = ceval(prj(val));
public default M[Entity] clookup(TVal[AstNode] t) = clookup(prj(t));
public default M[Entity] (Entity) cparam(TVal[int] i) = cparam(prj(i));
public default M[Entity] cdecl(TVal[Entity] val) = cdecl(prj(val));
public default M[PEntity] geval(TVal[PEntity] val) = geval(prj(val));
public default M[PEntity] glookup(TVal[AstNode] t) = glookup(prj(t));
public default M[PEntity] (PEntity) gparam(TVal[int] i) = gparam(prj(i));
public default M[PEntity] gdecl(TVal[PEntity] val) = gdecl(prj(val));
public default M[PEntity] cmkSubstsExplicit(TVal[Entity] val) = cmkSubstsExplicit(prj(val));
public default M[PEntity] filt1(TVal[PEntity] val) = filt1(prj(val));
public default M[PEntity] filt2(TVal[PEntity] val) = filt2(prj(val));
public default M[PEntity] filt3(TVal[PEntity] val) = filt3(prj(val));
public default M[PEntity] filt(bool (PEntity) p, TVal[PEntity] val) = filt(p, prj(val));
public default M[PEntity] parameterize11(TVal[PEntity] val1, TVal[PEntity] val2) = parameterize11(prj(val1), prj(val2));
public default M[PEntity] parameterize21(TVal[PEntity] val1, TVal[PEntity] val2) = parameterize21(prj(val1), prj(val2));
public default M[PEntity] parameterize22(TVal[PEntity] val) = parameterize22(prj(val));
//===================================
