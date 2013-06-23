@license{
  Copyright (c) 2009-2011 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Anastasia Izmaylova - A.Izmaylova@cwi.nl}
module prototype::computations::tests::TestProjects

public loc exmpl1 = |project://TyMoReCases/src/rawtypes/Example1.java|;
public loc exmpl2 = |project://TyMoReCases/src/rawtypes/Example2.java|;
public loc exmpl3 = |project://TyMoReCases/src/rawtypes/Example3.java|;
public loc exmpl4 = |project://TyMoReCases/src/rawtypes/Example4.java|;
public loc exmpl5 = |project://TyMoReCases/src/rawtypes/Example5.java|;
public loc exmpl5b = |project://TyMoReCases/src/rawtypes/Example5b.java|;
public loc exmpl6 = |project://TyMoReCases/src/rawtypes/Example6.java|;
public loc exmpl7 = |project://TyMoReCases/src/rawtypes/Example7.java|;
public loc exmpl8 = |project://TyMoReCases/src/rawtypes/Example8.java|;
public loc exmpl9 = |project://TyMoReCases/src/rawtypes/Example9.java|;
public loc exmpl10 = |project://TyMoReCases/src/rawtypes/Example10.java|;
public loc exmpl11 = |project://TyMoReCases/src/rawtypes/Example11.java|;
public loc exmpl11NonStatic = |project://TyMoReCases/src/Example11/Example11.java|;
public loc exmpl12 = |project://TyMoReCases/src/rawtypes/Example12.java|;
public loc exmpl13 = |project://TyMoReCases/src/rawtypes/Example13.java|;
public loc exmpl14 = |project://TyMoReCases/src/rawtypes/Example14.java|;
public loc exmpl15 = |project://TyMoReCases/src/rawtypes/Example15.java|;
public loc exmplG = |project://TyMoReCases/src/rawtypes/G.java|;

public loc wexmpl2 = |project://TyMoReCases/src/wildcards/Example2.java|;
public loc wexmpl3 = |project://TyMoReCases/src/wildcards/Example3.java|;
public loc wexmpl4 = |project://TyMoReCases/src/wildcards/Example4.java|;
public loc wexmpl6 = |project://TyMoReCases/src/wildcards/Example6.java|;
public loc wexmpl7 = |project://TyMoReCases/src/wildcards/Example7.java|;


public list[loc] testcases = [ exmpl1,
						 	   exmpl2,
						 	   exmpl3,
						 	   exmpl4,
						 	   exmpl5,
						 	   exmpl5b,
						 	   exmpl6,
						 	   exmpl7,
						 	   exmpl8,
						 	   exmpl9,
						 	   exmpl10 ];

//public loc testcases1 = |project://TyMoReTestCases/src|;
//public loc testcases2 = |project://TyMoReTestCasesWithoutWildCards/src|;
//public loc testcase1 = |project://LetsTryItOut/src|;
//public loc testcase2 = |project://LetsTryInitializersOut/src|;
//public loc testcase3 = |project://LetsTryLocalTypesOut/src|;
//public loc testcase4 = |project://LetsTryInitializerCounterOut/src|;
//public loc testcase5 = |project://LetsTryItOut/src/testcases|;

public list[loc] eclipseIMPSources = [
										|project://org.eclipse.imp.pdb/src|,
										|project://org.eclipse.imp.pdb.ui/src|,
										|project://org.eclipse.imp.pdb.values/src|,
										|project://org.eclipse.imp.runtime/src|
									 ];
public list[loc] antlrSources = [|project://antler/src|];
public list[loc] apacheAntSources = [|project://apache-ant/src/src/main|];
public list[loc] bcelSources = [|project://bcel/src/java|];
public list[loc] dsbudgetSources = [|project://dsbudget/src|];
public list[loc] tomcat70Sources = [|project://Tomcat70/src|];
public list[loc] xmlCommonsExternalSources = [|project://xml-commons-external/src|];
public list[loc] eclipseSources = [ 
									//|project://org.eclipse.core.resources.compatibility/src|,
									//|project://org.eclipse.e4.core.commands/src|,
									//|project://org.eclipse.e4.core.contexts/src|,
									//|project://org.eclipse.e4.core.contexts.debug/src|,
									//|project://org.eclipse.e4.core.deeplink/src|,
									//|project://org.eclipse.e4.core.deeplink.handler/src|,
									//|project://org.eclipse.e4.core.deeplink.launchproxy/src|,
									//|project://org.eclipse.e4.core.deeplink.typehandler.extensionpt/src|,
									//|project://org.eclipse.e4.core.di/src|,
									//|project://org.eclipse.e4.core.di.extensions/src|,
									//|project://org.eclipse.e4.core.functionalprog/src|,
									//|project://org.eclipse.e4.core.javascript/src|,
									//|project://org.eclipse.e4.core.metaconfig/src|,
									//|project://org.eclipse.e4.core.services/src|,
									//|project://org.eclipse.e4.emf.javascript/src|,
									//|project://org.eclipse.e4.emf.javascript.ui/src|,
									//|project://org.eclipse.e4.emf.xpath/src|,
									//|project://org.eclipse.e4.enterprise.installer/src|,
									//|project://org.eclipse.e4.enterprise.installer.ui.swt/src|,
									//|project://org.eclipse.e4.javascript/src|,
									//|project://org.eclipse.e4.javascript.registry/src|,
									//|project://org.eclipse.e4.languages.javascript/src|,
									//|project://org.eclipse.e4.languages.javascript.debug.connect/src|,
									//|project://org.eclipse.e4.languages.javascript.debug.jsdi/src|,
									//|project://org.eclipse.e4.languages.javascript.debug.jsdi.rhino/src|,
									//|project://org.eclipse.e4.languages.javascript.debug.model/src|,
									//|project://org.eclipse.e4.languages.javascript.debug.rhino/src|,
									//|project://org.eclipse.e4.languages.javascript.debug.ui/src|,
									//|project://org.eclipse.e4.languages.javascript.js/src|,
									//|project://org.eclipse.e4.languages.javascript.junit/src|,
									//|project://org.eclipse.e4.languages.javascript.registry/src|,
									//|project://org.eclipse.e4.pde.ui/src|,
									//|project://org.eclipse.e4.pde.webui/src|,
									//|project://org.eclipse.e4.server.bespin/src|,
									//|project://org.eclipse.e4.tm/src|,
									//|project://org.eclipse.e4.tm.builder/src|,
									//|project://org.eclipse.e4.tm.graphics/src|,
									//|project://org.eclipse.e4.tm.ui/src|,
									//|project://org.eclipse.e4.ui.bindings/src|,
									//|project://org.eclipse.e4.ui.css.core/src|,
									//|project://org.eclipse.e4.ui.css.jface/src|,
									//|project://org.eclipse.e4.ui.css.legacy/src|,
									//|project://org.eclipse.e4.ui.css.swt/src|,
									//|project://org.eclipse.e4.ui.css.swt.theme/src|,
									//|project://org.eclipse.e4.ui.deeplink.typehandler.perspective/src|,
									//|project://org.eclipse.e4.ui.di/src|,
									//|project://org.eclipse.e4.ui.di/src|,
									//|project://org.eclipse.e4.ui.gadgets/src|,
									//|project://org.eclipse.e4.ui.model.workbench/src|,
									//|project://org.eclipse.e4.ui.model.workbench.edit/src|,
									//|project://org.eclipse.e4.ui.services/src|,
									//|project://org.eclipse.e4.ui.swtdialogs/src|,
									//|project://org.eclipse.e4.ui.web/src|,
									//|project://org.eclipse.e4.ui.widgets/src|,
									//|project://org.eclipse.e4.ui.workbench/src|, // huge
									//|project://org.eclipse.e4.ui.workbench.addons.swt/src|,
									//|project://org.eclipse.e4.ui.workbench.renderers.swt/src|,
									//|project://org.eclipse.e4.ui.workbench.renderers.swt.cocoa/src|,
									//|project://org.eclipse.e4.ui.workbench.swt/src|,
									//|project://org.eclipse.e4.ui.workbench3/src|,
									//|project://org.eclipse.e4.xwt/src|,
									//|project://org.eclipse.e4.xwt.css/src|,
									//|project://org.eclipse.e4.xwt.emf/src|,
									//|project://org.eclipse.e4.xwt.forms/src|,
									//|project://org.eclipse.e4.xwt.pde/src|,
									//|project://org.eclipse.e4.xwt.springframework/src|,
									//|project://org.eclipse.e4.xwt.tools.categorynode/src|,
									//|project://org.eclipse.e4.xwt.tools.categorynode.edit/src|,
									//|project://org.eclipse.e4.xwt.tools.ui/src|,
									//|project://org.eclipse.e4.xwt.tools.ui.designer/src|,
									//|project://org.eclipse.e4.xwt.tools.ui.designer.core/src|,
									//|project://org.eclipse.e4.xwt.tools.ui.editor/src|,									
									//|project://org.eclipse.e4.xwt.tools.ui.imagecapture/src|,
									//|project://org.eclipse.e4.xwt.tools.ui.palette/src|,
									//|project://org.eclipse.e4.xwt.tools.ui.xaml/src|,
									//|project://org.eclipse.e4.xwt.ui.workbench/src|,
									//|project://org.eclipse.e4.xwt.vex/src|,
									//|project://org.eclipse.e4.xwt.xml/src|,
									//|project://org.eclipse.jdt.compiler.as/src|,
									//|project://org.eclipse.wst.jsdt.core/src|, // huge
									//|project://org.eclipse.wst.jsdt.debug.rhino.debugger/src|,
									//|project://org.eclipse.wst.jsdt.debug.transport/src|,
									//|project://org.eclipse.wst.jsdt.manipulation/src|,
									//|project://org.eclipse.wst.jsdt.ui/src|,								
								    //|project://org.pushingpixels.trident/src|
								    ];
