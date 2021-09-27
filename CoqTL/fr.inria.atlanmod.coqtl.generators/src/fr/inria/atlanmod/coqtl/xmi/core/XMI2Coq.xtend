package fr.inria.atlanmod.coqtl.xmi.core

import java.util.HashSet
import java.util.Set
import org.eclipse.emf.common.util.EList
import org.eclipse.emf.ecore.EObject
import org.eclipse.emf.ecore.impl.DynamicEObjectImpl
import org.eclipse.emf.ecore.EReference
import fr.inria.atlanmod.coqtl.util.Keywords
import org.eclipse.emf.ecore.EAttribute
import org.eclipse.emf.ecore.EStructuralFeature
import fr.inria.atlanmod.coqtl.util.EMFUtil
import org.eclipse.emf.ecore.EClass
import java.text.SimpleDateFormat
import java.util.Date
import org.eclipse.emf.ecore.util.EcoreUtil

class XMI2Coq {
  
	Set<Object> lookup;
	
  	new() {
    	lookup = new HashSet<Object>
  	}
	
	
	/* 
	 * Entry point of model to Boogie transformation
	 * */ 
	def mapEObjects(EList<EObject> eobjects, String ns, String meta) '''
		(********************************************************************
			@name Coq declarations for model
			@date «new SimpleDateFormat("yyyy/MM/dd HH:mm:ss").format(new Date)»
			@description Automatically generated by XMI2Coq transformation.
		 ********************************************************************)
				 
		Require Import List.
		Require Import core.Model.
		Require Import String.
		Require Import examples.«ns».«meta».
		
		«var allEObjects = new HashSet»
		«val root = eobjects.get(0)»
		«val mm = root.eClass.EPackage.name+Keywords.PostfixMetamodel»
		«val mm_eobject = '''«mm»_«Keywords.PostfixEObject»'''»
		«val mm_elink = '''«mm»_«Keywords.PostfixELink»'''»
		
		«FOR eobject: eobjects.filter(typeof(EObject))»		
			«val ignore = allEObjects.addAll(getAllEObjects(eobject))»		
		«ENDFOR»
		Definition InputModel : Model «mm_eobject» «mm_elink» :=
			(Build_Model
				(
				«FOR eobject : allEObjects»
				(Build_«mm_eobject» «BuildTopSuperEClass(eobject.eClass)» «BuildEObject(eobject, eobject.eClass)») :: 
				«ENDFOR»
				nil)
				(
				«FOR eobject : allEObjects»
				«FOR sf : eobject.eClass.EStructuralFeatures.filter(typeof(EReference))»«val sf_value = eobject.eGet(sf)»«IF sf_value != null»
				(Build_«mm_elink» «eobject.eClass.name»«sf.name.toFirstUpper»«Keywords.PostfixEReference» «BuildELink(eobject, sf)») ::
				«ENDIF»
				«ENDFOR»
				«ENDFOR» 
				nil)
			).
	'''
	
	def BuildTopSuperEClass(EClass eClass) '''
	«IF eClass.ESuperTypes.size > 0 »«BuildTopSuperEClass(eClass.ESuperTypes.get(0))»«ELSE»«eClass.name»«Keywords.PostfixEClass»«ENDIF»'''
	
	def BuildSuperEObject_prefix(EClass eSupClass, EClass eSubClass) '''
	«IF eSupClass.ESuperTypes.size > 0 »«BuildSuperEObject_prefix(eSupClass.ESuperTypes.get(0), eSupClass)»«ENDIF
	»(Build_Abstract_«eSupClass.name» «eSubClass.name»«Keywords.PostfixEClass» '''
	
	def BuildSuperEObject_surfix(EClass eClass) '''
	«IF eClass.ESuperTypes.size > 0 »«BuildSuperEObject_surfix(eClass.ESuperTypes.get(0))»«ENDIF»)'''
	
	def BuildEObject(EObject eObject, EClass eClass) '''
	«IF eClass.ESuperTypes.size>0»«BuildSuperEObject_prefix(eClass.ESuperTypes.get(0), eClass)»«ENDIF
	»(Build«eClass.name» "«System.identityHashCode(eObject)+"_"+eClass.name»" «FOR sf: eClass.EAllAttributes SEPARATOR " "»«EMFUtil.PrintValue(eObject.eGet(sf))»«ENDFOR»)«
	IF eClass.ESuperTypes.size>0»«BuildSuperEObject_surfix(eClass.ESuperTypes.get(0))»«ENDIF»'''
			
	def BuildELink(EObject eobject, EStructuralFeature sf)'''
		«val sf_value = eobject.eGet(sf)»«val tp = sf.EType as EClass»
		(Build«eobject.eClass.name»«sf.name.toFirstUpper» «BuildEObject_inref(eobject, eobject.eClass)» «BuildEReference(sf_value, tp)»)'''
	
	def BuildEObject_inref(EObject eObject, EClass eClass) '''
	«IF eClass.isAbstract
	»«IF eObject.eClass.ESuperTypes.size>0»«BuildSuperEObject_inref_prefix(eObject.eClass.ESuperTypes.get(0), eObject.eClass, eClass)»«ENDIF
	» (Build«eObject.eClass.name» "«System.identityHashCode(eObject)+"_"+eClass.name»" «FOR sf: eClass.EAllAttributes SEPARATOR " "»«EMFUtil.PrintValue(eObject.eGet(sf))»«ENDFOR») «
	IF eObject.eClass.ESuperTypes.size>0»«BuildSuperEObject_inref_surfix(eObject.eClass, eClass)»«ENDIF»«
	ELSE» (Build«eObject.eClass.name» "«System.identityHashCode(eObject)+"_"+eClass.name»" «FOR sf: eClass.EAllAttributes SEPARATOR " "»«EMFUtil.PrintValue(eObject.eGet(sf))»«ENDFOR»)«ENDIF»'''
	
	def BuildSuperEObject_inref_prefix(EClass eSupClass, EClass eSubClass, EClass top) '''
	«IF eSupClass.ESuperTypes.size > 0 && eSupClass.name != top.name»«BuildSuperEObject_inref_prefix(eSupClass.ESuperTypes.get(0), eSupClass, top)» «ENDIF
	» (Build_Abstract_«eSupClass.name» «eSubClass.name»«Keywords.PostfixEClass» '''
	
	def BuildSuperEObject_inref_surfix(EClass eClass, EClass top) '''
	«IF eClass.ESuperTypes.size > 0 && eClass.ESuperTypes.get(0).name != top.name »«BuildSuperEObject_inref_surfix(eClass.ESuperTypes.get(0), top)»«ENDIF»)'''
	
	
	//TODO pick up back reference?
	def BuildEReference(Object sf_value, EClass tp) '''
		«IF sf_value instanceof EList 
		»«IF sf_value.size > 0»(«FOR v : sf_value.filter(typeof(EObject)) SEPARATOR " :: "»«BuildEObject_inref(v, tp)»«ENDFOR» :: nil )«ELSE» nil «ENDIF»«
		ELSEIF sf_value instanceof EObject
		»«BuildEObject_inref(sf_value as EObject, tp)»«
		ENDIF»'''
	
	def HashSet<EObject> getAllEObjects(EObject o) {
		var rtn = new HashSet
		
		if(!this.lookup.contains(o) && o instanceof DynamicEObjectImpl){
			val eobject = o as DynamicEObjectImpl
			rtn.add(eobject)
			this.lookup.add(eobject)
				
			for(sf : eobject.eClass.EStructuralFeatures.filter(typeof(EReference))){
				val sf_value = eobject.eGet(sf)
				
				if(sf_value instanceof EList){
					for(v : sf_value.filter(typeof(EObject))){
						rtn.addAll(getAllEObjects(v))
					}
				}else if(sf_value instanceof EObject){
					rtn.addAll(getAllEObjects(sf_value))
				}
			}
		}
		
		return rtn
	}
	
}
