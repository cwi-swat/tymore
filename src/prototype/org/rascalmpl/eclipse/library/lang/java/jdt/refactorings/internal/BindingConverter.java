/*******************************************************************************
 * Copyright (c) 2009-2012 CWI
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *   * Anastasia Izmaylova - A.Izmaylova@cwi.nl - CWI
 *******************************************************************************/
package prototype.org.rascalmpl.eclipse.library.lang.java.jdt.refactorings.internal;

import org.eclipse.imp.pdb.facts.IList;
import org.eclipse.imp.pdb.facts.IListWriter;
import org.eclipse.imp.pdb.facts.IValue;
import org.eclipse.imp.pdb.facts.IValueFactory;
import org.eclipse.imp.pdb.facts.type.Type;
import org.eclipse.imp.pdb.facts.type.TypeFactory;
import org.eclipse.imp.pdb.facts.type.TypeStore;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.rascalmpl.values.ValueFactoryFactory;
/*
 * Extends the 'BindingConverter' to convert to the entities with enriched type information  
 */
public class BindingConverter extends org.rascalmpl.eclipse.library.lang.java.jdt.internal.BindingConverter {
	
	private static final IValueFactory VF = ValueFactoryFactory.getValueFactory();
	private static final TypeFactory TF = TypeFactory.getInstance();
	private static final TypeStore store = new TypeStore();
	
	public static final Type ADT_ID = TF.abstractDataType(store, "Id");
	public static final Type ADT_ENTITY = TF.abstractDataType(store, "Entity");
	
	/*
	 * Java entities with enriched type information
	 */
	public static final Type CONS_GENERIC_METHOD = TF.constructor(store, ADT_ID, "method", TF.listType(ADT_ENTITY), 
																				 "genericTypes", TF.stringType(), // '+' generic types
																				 "name", TF.listType(ADT_ENTITY), 
																				 "params", ADT_ENTITY, 
																				 "returnType");
	public static final Type CONS_GENERIC_CONSTRUCTOR = TF.constructor(store, ADT_ID, "constr", TF.listType(ADT_ENTITY), 
																					  "genericTypes", TF.listType(ADT_ENTITY), // '+' generics
																					  "params");
	public static final Type CONS_ENUM_CONSTANT_TYPED = TF.constructor(store, ADT_ID, "enumConstant", TF.stringType(), 
																					  "name", ADT_ENTITY, 
																					  "declaredType"); // '+' declared type
	public static final Type CONS_FIELD_TYPED = TF.constructor(store, ADT_ID, "field", TF.stringType(), 
																			  "name", ADT_ENTITY, 
																			  "declaredType"); // '+' declared type
	public static final Type CONS_PARAMETER_TYPED = TF.constructor(store, ADT_ID, "parameter", TF.stringType(), 
																				  "name", ADT_ENTITY, 
																				  "declaredType"); // '+' declared type
	public static final Type CONS_VARIABLE_TYPED = TF.constructor(store, ADT_ID, "variable", TF.stringType(), 
																				 "name", ADT_ENTITY, 
																				 "declaredType", TF.integerType(),  // '+' declared type
																				 "id");
	public static final Type CONS_TYPE_PARAMETER_BOUNDED = TF.constructor(store, ADT_ID, "typeParameter", TF.stringType(), 
																						 "name", TF.listType(ADT_ENTITY), 
																						 "bounds"); // '+' bounds (problematic due to cycles)
		
	public IValue getId(IMethodBinding mb) {
		 // Takes into account type parameters and type arguments of generic and parameterized methods	
		if(mb.isGenericMethod()) {
			if (mb.isConstructor()) 
				return VF.constructor(CONS_GENERIC_CONSTRUCTOR, getEntities(mb.getTypeParameters()), getEntities(mb.getParameterTypes()));
			else
				return VF.constructor(CONS_GENERIC_METHOD, getEntities(mb.getTypeParameters()), VF.string(mb.getName()), getEntities(mb.getParameterTypes()), getEntity(mb.getReturnType()));
		} else if(mb.isParameterizedMethod()) {
			if (mb.isConstructor())
				return VF.constructor(CONS_GENERIC_CONSTRUCTOR, getEntities(mb.getTypeArguments()), getEntities(mb.getParameterTypes()));
			else
				return VF.constructor(CONS_GENERIC_METHOD, getEntities(mb.getTypeArguments()), VF.string(mb.getName()), getEntities(mb.getParameterTypes()), getEntity(mb.getReturnType()));
		} 
		return super.getId(mb);
	}
	
	public IValue getId(ITypeBinding tb) {
		if(!tb.isTypeVariable()) return super.getId(tb);
		// Unique type parameter names '+' bounds (problematic due to cycles)
		return VF.constructor(CONS_TYPE_PARAMETER_BOUNDED, VF.string(tb.getName() + tb.getKey().hashCode())); 
	}
	
	public IValue getId(IVariableBinding vb) {
		if(vb.isEnumConstant()) {
			return VF.constructor(CONS_ENUM_CONSTANT_TYPED, VF.string(vb.getName()), getEntity(vb.getType(), null));
		} else if(vb.isField()) {
			return VF.constructor(CONS_FIELD_TYPED, VF.string(vb.getName()), getEntity(vb.getType(), null));
		} else if(vb.isParameter()) {
			return VF.constructor(CONS_PARAMETER_TYPED, VF.string(vb.getName()), getEntity(vb.getType(), null));
		} 
		// local variable
		return VF.constructor(CONS_VARIABLE_TYPED, VF.string(vb.getName()), getEntity(vb.getType(), null), VF.integer(vb.getVariableId()));
	}
	
	@SuppressWarnings("deprecation")
	public IList getEntities(ITypeBinding[] tbs) {
		IListWriter params = VF.listWriter(ADT_ENTITY);
		for(ITypeBinding tb : tbs) 
			params.append(getEntity(tb));
		return params.done();
	}
	
}