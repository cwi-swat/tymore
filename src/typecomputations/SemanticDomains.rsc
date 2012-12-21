module typecomputations::SemanticDomains

import lang::java::jdt::Java;
import lang::java::jdt::JavaADT;
import lang::java::jdt::refactorings::Java;
import lang::java::jdt::refactorings::JavaADT;
import lang::java::jdt::refactorings::PrettyPrintUtil;

import Prelude;


@doc{Semantic domain that allows overriding of the basic semantic functions on program terms}
data TVal[&V] = wrapval(&V v)
			  | nestval(TVal[&V] tv)
			  ;
	   
public TVal[&V] inj(&V val) = nestval(nestval(wrapval(val)));
public TVal[&V] inj1(&V val) = wrapval(val);

public default TVal[&V] prj(TVal[&V] val) = val;
public TVal[&V] prj(nestval(TVal[&V] val)) = val;

public default &V prjAll(&V val) = val;
public &V prjAll(wrapval(&V val)) = val;
public &V prjAll(nestval(TVal[&V] val)) = prjAll(val);
