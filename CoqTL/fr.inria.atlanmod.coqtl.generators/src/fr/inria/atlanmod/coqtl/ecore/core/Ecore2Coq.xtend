package fr.inria.atlanmod.coqtl.ecore.core

import fr.inria.atlanmod.coqtl.util.EMFUtil
import java.text.SimpleDateFormat
import java.util.Date
import org.eclipse.emf.ecore.EAttribute
import org.eclipse.emf.ecore.EClass
import org.eclipse.emf.ecore.EObject
import org.eclipse.emf.ecore.EPackage
import org.eclipse.emf.ecore.EReference
import fr.inria.atlanmod.coqtl.util.Keywords
import java.util.HashSet

class Ecore2Coq {
	
			
				
				
	/* 
	 * Entry point of metamodel to Boogie transformation
	 * */ 
	def static mapEPackage(EPackage ePackage) '''

		(********************************************************************
			@name Coq declarations for metamodel: <«ePackage.name»>
			@date «new SimpleDateFormat("yyyy/MM/dd HH:mm:ss").format(new Date)»
			@description Automatically generated by Ecore2Coq transformation.
		 ********************************************************************)
		
		(* Coq libraries *)
		Require Import String.
		Require Import List.      (* sequence *)
		Require Import Multiset.  (* bag *)
		Require Import ListSet.   (* set *)
		Require Import Omega.
		Require Import Bool.
		
		Require Import core.utils.TopUtils.
		Require Import core.Metamodel.
		Require Import core.Model.
		
		Require Import Coq.Logic.Eqdep_dec.

		(* Base types *)
		«FOR eClass : ePackage.EClassifiers.filter(typeof(EClass))»
			Inductive «eClass.name» : Set :=
			  Build«eClass.name» :
			  «IF eClass.ESuperTypes.size>0»(* Inheritence Attribute *) «eClass.ESuperTypes.get(0).name» -> «ENDIF»
			  (* id *) string ->
			  «FOR eAttribute : eClass.EAttributes»
			    (* «eAttribute.name» *) «AttributeType2Coq(eAttribute)» ->
			  «ENDFOR»
			  «eClass.name».
			  
		«ENDFOR»	
		
		«FOR eClass : ePackage.EClassifiers.filter(typeof(EClass))»
 			«FOR eReference : eClass.EReferences
            »Inductive «eClass.name»«eReference.name.toFirstUpper» : Set :=
 			   Build«eClass.name»«eReference.name.toFirstUpper» :
 			   «eClass.name» ->
 			   «ReferenceType2Coq(eReference)» ->
 			   «eClass.name»«eReference.name.toFirstUpper».
			«ENDFOR»

		«ENDFOR»
		
		
		(* Accessors *)
		«FOR eClass : ePackage.EClassifiers.filter(typeof(EClass))»
			  «val v = eClass.name.toLowerCase.charAt(0)»
			  «IF eClass.ESuperTypes.size>0»
			  «val supName = eClass.ESuperTypes.get(0).name»
			  Definition «eClass.name»_get«supName.toFirstUpper» («v» : «eClass.name») : «supName» :=
			    match «v» with Build«eClass.name» «IF eClass.ESuperTypes.size>0»«supName.toLowerCase»«ENDIF» id «FOR eAttributeCtr : eClass.EAttributes»«eAttributeCtr.name» «ENDFOR» => «supName.toLowerCase» end.
			  «ENDIF»	
			  Definition «eClass.name»_getId («v» : «eClass.name») : string :=
			    match «v» with Build«eClass.name» «IF eClass.ESuperTypes.size>0»«eClass.ESuperTypes.get(0).name.toLowerCase»«ENDIF» id «FOR eAttributeCtr : eClass.EAttributes»«eAttributeCtr.name» «ENDFOR» => id end.
			  «FOR eAttribute : eClass.EAttributes»
			  Definition «eClass.name»_get«eAttribute.name.toFirstUpper» («v» : «eClass.name») : «AttributeType2Coq(eAttribute)» :=
			    match «v» with Build«eClass.name» «IF eClass.ESuperTypes.size>0»«eClass.ESuperTypes.get(0).name.toLowerCase»«ENDIF» id «FOR eAttributeCtr : eClass.EAttributes»«eAttributeCtr.name» «ENDFOR» => «eAttribute.name» end.
			  «ENDFOR»	 
			   
		«ENDFOR»


				
		(* Meta-types *)
		Inductive «ePackage.name»«Keywords.PostfixMetamodel»_«Keywords.PostfixEClass» : Set :=
		  «FOR eClass : ePackage.EClassifiers.filter(typeof(EClass))»
		  | «eClass.name»«Keywords.PostfixEClass»
		  «ENDFOR»
		.
		
		«val farg_getTypeByEClass = arg('''«ePackage.name»«Keywords.PostfixMetamodel»_«Keywords.PostfixEClass»''')»
		Definition «ePackage.name»«Keywords.PostfixMetamodel»_getTypeByEClass («farg_getTypeByEClass» : «ePackage.name»«Keywords.PostfixMetamodel»_«Keywords.PostfixEClass») : Set :=
		  match «farg_getTypeByEClass» with
		    «FOR eClass : ePackage.EClassifiers.filter(typeof(EClass))»
		    | «eClass.name»«Keywords.PostfixEClass» => «eClass.name»
		    «ENDFOR»
		  end.	
		
		«val farg_getEAttributeTypesByEClass = arg('''«ePackage.name»«Keywords.PostfixMetamodel»_«Keywords.PostfixEClass»''')»
		Definition «ePackage.name»«Keywords.PostfixMetamodel»_getEAttributeTypesByEClass («farg_getEAttributeTypesByEClass» : «ePackage.name»«Keywords.PostfixMetamodel»_«Keywords.PostfixEClass») : Set :=
		  match «farg_getEAttributeTypesByEClass» with
		    «FOR eClass : ePackage.EClassifiers.filter(typeof(EClass))»
		    | «eClass.name»«Keywords.PostfixEClass» => 
		    «IF eClass.ESuperTypes.size > 0 »
		    	«IF eClass.EAttributes.size > 0»
		    	(«eClass.ESuperTypes.get(0).name» * «FOR eAttributeCtr : eClass.EAttributes SEPARATOR " * "»«AttributeType2Coq(eAttributeCtr)»«ENDFOR»)
		    	«ELSE»
		    	(«eClass.ESuperTypes.get(0).name»)
		    	«ENDIF»
		    «ELSE»
		    	«IF eClass.EAttributes.size > 0»
		    	(«FOR eAttributeCtr : eClass.EAttributes SEPARATOR " * "»«AttributeType2Coq(eAttributeCtr)»«ENDFOR»)
		    	«ELSE»
		    	(Empty_set)
		    	«ENDIF»
		    «ENDIF»
			«ENDFOR»
		  end.
		
		Inductive «ePackage.name»«Keywords.PostfixMetamodel»_«Keywords.PostfixEReference» : Set :=
		  «FOR eClass : ePackage.EClassifiers.filter(typeof(EClass))»
			«FOR eReference : eClass.EReferences
		    »| «eClass.name»«eReference.name.toFirstUpper»«Keywords.PostfixEReference»
		 	«ENDFOR»
		  «ENDFOR»
		.
		
		«val farg_getTypeByEReference = arg('''«ePackage.name»«Keywords.PostfixMetamodel»_«Keywords.PostfixEReference»''')»
		Definition «ePackage.name»«Keywords.PostfixMetamodel»_getTypeByEReference («farg_getTypeByEReference» : «ePackage.name»«Keywords.PostfixMetamodel»_«Keywords.PostfixEReference») : Set :=
		  match «farg_getTypeByEReference» with
		    «FOR eClass : ePackage.EClassifiers.filter(typeof(EClass))»
				«FOR eReference : eClass.EReferences
    		    »| «eClass.name»«eReference.name.toFirstUpper»«Keywords.PostfixEReference» => «eClass.name»«eReference.name.toFirstUpper»
    		 	«ENDFOR» 
		    «ENDFOR»
		  end.
		
		«val farg_getERoleTypesByEReference = arg('''«ePackage.name»«Keywords.PostfixMetamodel»_«Keywords.PostfixEReference»''')»
		Definition «ePackage.name»«Keywords.PostfixMetamodel»_getERoleTypesByEReference («farg_getERoleTypesByEReference» : «ePackage.name»«Keywords.PostfixMetamodel»_«Keywords.PostfixEReference») : Set :=
		  match «farg_getERoleTypesByEReference» with
		    «FOR eClass : ePackage.EClassifiers.filter(typeof(EClass))»
				«FOR eReference : eClass.EReferences
		    	»| «eClass.name»«eReference.name.toFirstUpper»«Keywords.PostfixEReference» => («eClass.name» * «ReferenceType2Coq(eReference)»)
		    	«ENDFOR»
		    «ENDFOR»
		  end.
		
		(* Generic types *)
		«val mm = '''«ePackage.name»«Keywords.PostfixMetamodel»'''»
		«val mm_eclass = '''«mm»_«Keywords.PostfixEClass»'''»
		«val mm_eclass_qarg = arg('''«mm»_«Keywords.PostfixEClass»''')»
		«val mm_eclass_qarg1 = arg1('''«mm»_«Keywords.PostfixEClass»''')»
		«val mm_eclass_qarg2 = arg2('''«mm»_«Keywords.PostfixEClass»''')»
		
		«val mm_eref = '''«mm»_«Keywords.PostfixEReference»'''»
		«val mm_eref_qarg = arg('''«mm»_«Keywords.PostfixEReference»''')»
		«val mm_eref_qarg1 = arg1('''«mm»_«Keywords.PostfixEReference»''')»
		«val mm_eref_qarg2 = arg2('''«mm»_«Keywords.PostfixEReference»''')»
		
		«val mm_eobject = '''«mm»_«Keywords.PostfixEObject»'''»
		«val mm_eobject_qarg = arg('''«mm»_«Keywords.PostfixEObject»''')»
		
		«val mm_elink = '''«mm»_«Keywords.PostfixELink»'''»
		«val mm_elink_qarg = arg('''«mm»_«Keywords.PostfixELink»''')»
		
		«val larg = '''p'''»
		
		Inductive «mm_eobject» : Set :=
		 | Build_«mm_eobject» : 
		    forall («mm_eclass_qarg»: «mm_eclass»), («ePackage.name»«Keywords.PostfixMetamodel»_getTypeByEClass «mm_eclass_qarg») -> «mm_eobject».
		
		Inductive «mm_elink» : Set :=
		 | Build_«mm_elink» : 
		    forall («mm_eref_qarg»:«mm_eref»), («ePackage.name»«Keywords.PostfixMetamodel»_getTypeByEReference «mm_eref_qarg») -> «mm_elink».
		
		(* Reflective functions *)

		Lemma «mm»_eqEClass_dec : 
		 forall («mm_eclass_qarg1»:«mm_eclass») («mm_eclass_qarg2»:«mm_eclass»), { «mm_eclass_qarg1» = «mm_eclass_qarg2» } + { «mm_eclass_qarg1» <> «mm_eclass_qarg2» }.
		Proof. repeat decide equality. Defined.
		
		Lemma «mm»_eqEReference_dec : 
		 forall («mm_eref_qarg1»:«mm_eref») («mm_eref_qarg2»:«mm_eref»), { «mm_eref_qarg1» = «mm_eref_qarg2» } + { «mm_eref_qarg1» <> «mm_eref_qarg2» }.
		Proof. repeat decide equality. Defined.
		
		Definition «mm»_getEClass («mm_eobject_qarg» : «mm_eobject») : «mm_eclass» :=
		   match «mm_eobject_qarg» with
		  | (Build_«mm_eobject» «mm_eobject_qarg» _) => «mm_eobject_qarg»
		   end.
		
		Definition «mm»_getEReference («mm_elink_qarg» : «mm_elink») : «mm_eref» :=
		   match «mm_elink_qarg» with
		  | (Build_«mm_elink» «mm_elink_qarg» _) => «mm_elink_qarg»
		   end.
		
		Definition «mm»_instanceOfEClass («mm_eclass_qarg»: «mm_eclass») («mm_eobject_qarg» : «mm_eobject»): bool :=
		  if «mm»_eqEClass_dec («mm»_getEClass «mm_eobject_qarg») «mm_eclass_qarg» then true else false.
		
		Definition «mm»_instanceOfEReference («mm_eref_qarg»: «mm_eref») («mm_elink_qarg» : «mm_elink»): bool :=
		  if «mm»_eqEReference_dec («mm»_getEReference «mm_elink_qarg») «mm_eref_qarg» then true else false.

		
		Definition «mm»_toEClass («mm_eclass_qarg» : «mm_eclass») («mm_eobject_qarg» : «mm_eobject») : option («mm»_getTypeByEClass «mm_eclass_qarg»).
		Proof.
		  destruct «mm_eobject_qarg» as [arg1 arg2].
		  destruct («mm»_eqEClass_dec arg1 «mm_eclass_qarg») as [e|] eqn:dec_case.
		  - rewrite e in arg2.
		    exact (Some arg2).
		  - exact None.
		Defined.
		
		Definition «mm»_toEReference («mm_eref_qarg» : «mm_eref») («mm_elink_qarg» : «mm_elink») : option («mm»_getTypeByEReference «mm_eref_qarg»).
		Proof.
		  destruct «mm_elink_qarg» as [arg1 arg2].
		  destruct («mm»_eqEReference_dec arg1 «mm_eref_qarg») as [e|] eqn:dec_case.
		  - rewrite e in arg2.
		  	exact (Some arg2).
		  - exact None.
		Defined.
		
		(* Generic functions *)
		«FOR eClass : ePackage.EClassifiers.filter(typeof(EClass))»
			Definition «mm»_toEObjectFrom«eClass.name» («arg(eClass.name)» :«eClass.name») : «mm_eobject» :=
			  (Build_«mm_eobject» «eClass.name»«Keywords.PostfixEClass» «arg(eClass.name)»).
			Coercion «mm»_toEObjectFrom«eClass.name» : «eClass.name» >-> «mm_eobject».

		«ENDFOR»
		
		(** Metamodel Type Class Instaniation **)
		Definition «mm»_toEObject («mm_eobject_qarg» : «mm_eobject») : «mm_eobject» := «mm_eobject_qarg».
		Definition «mm»_toELink («mm_elink_qarg» : «mm_elink») : «mm_elink» := «mm_elink_qarg».
		Definition «ePackage.name»Model := Model «mm_eobject» «mm_elink».
		
		Definition «mm»_toEObjectOfEClass («mm_eclass_qarg»: «mm_eclass») (t: «mm»_getTypeByEClass «mm_eclass_qarg») : «mm_eobject» :=
		  (Build_«mm_eobject» «mm_eclass_qarg» t).
		
		Definition «mm»_toELinkOfEReference («mm_eref_qarg»: «mm_eref») (t: «mm»_getTypeByEReference «mm_eref_qarg») : «mm_elink» :=
				  (Build_«mm_elink» «mm_eref_qarg» t).
		
		
		(* Accessors on model *)
		(* Equality for Types *)
		(*? We currently define eq for Eclass on their fist attribute *)
		«FOR eClass : ePackage.EClassifiers.filter(typeof(EClass))
		»Definition beq_«eClass.name» («arg1(eClass.name)» : «eClass.name») («arg2(eClass.name)» : «eClass.name») : bool :=
			«IF eClass.ESuperTypes.size > 0 »
		    	«val supName = eClass.ESuperTypes.get(0).name»
		    	«val supAcc = eClass.name+"_get"+supName.toFirstUpper»
		    	«IF eClass.EAttributes.size > 0»
		    	beq_«eClass.ESuperTypes.get(0).name» («supAcc» «arg1(eClass.name)») («supAcc» «arg2(eClass.name)») &&
		    	«FOR eAttribute : eClass.EAttributes SEPARATOR " && "
		    	»( beq_«AttributeType2Coq(eAttribute)» («eClass.name»_get«eAttribute.name.toFirstUpper» «arg1(eClass.name)») («eClass.name»_get«eAttribute.name.toFirstUpper» «arg2(eClass.name)») )
				«ENDFOR»
		    	«ELSE»
		    	beq_«eClass.ESuperTypes.get(0).name» («supAcc» «arg1(eClass.name)») («supAcc» «arg2(eClass.name)»)
		    	«ENDIF»
		    «ELSE»
		    	«IF eClass.EAttributes.size > 0»
		    	«FOR eAttribute : eClass.EAttributes SEPARATOR " && "
		    	»( beq_«AttributeType2Coq(eAttribute)» («eClass.name»_get«eAttribute.name.toFirstUpper» «arg1(eClass.name)») («eClass.name»_get«eAttribute.name.toFirstUpper» «arg2(eClass.name)») )
				«ENDFOR»
		    	«ELSE»
		    	(true)
		    	«ENDIF»
		    «ENDIF»
		.
		
		«ENDFOR»
		
		«val candidates = new HashSet»
		«FOR eSuper : ePackage.EClassifiers.filter(typeof(EClass))»
			«FOR eSub : ePackage.EClassifiers.filter(typeof(EClass))»
				«IF eSub.ESuperTypes.contains(eSuper)»
				«{candidates.add(eSuper);""}»
				«ENDIF»
			«ENDFOR»
		«ENDFOR»

		«FOR eSuper : candidates»
		   «FOR eSub : ePackage.EClassifiers.filter(typeof(EClass))»«IF eSub.ESuperTypes.contains(eSuper)
		   »Fixpoint «mm»_«eSuper.name»_downcast«eSub.name» («arg(eSuper.name)» : «eSuper.name») (l : list «mm_eobject») : option «eSub.name» := 
		     match l with
		   	 | Build_«mm_eobject» «eSub.name»«Keywords.PostfixEClass» (Build«eSub.name» eSuper id «FOR eAttributeCtr : eSub.EAttributes»«eAttributeCtr.name» «ENDFOR») :: l' => 
		   		if beq_«eSuper.name» «arg(eSuper.name)» eSuper then (Some (Build«eSub.name» eSuper id «FOR eAttributeCtr : eSub.EAttributes»«eAttributeCtr.name» «ENDFOR»)) else («mm»_«eSuper.name»_downcast«eSub.name» «arg(eSuper.name)» l')
		   	 | _ :: l' => («mm»_«eSuper.name»_downcast«eSub.name» «arg(eSuper.name)» l')
		   	 | nil => None
		   end.
		   
		   Definition «eSuper.name»_downcast«eSub.name» («arg(eSuper.name)» : «eSuper.name») (m : «ePackage.name»Model) : option «eSub.name» :=
		     «mm»_«eSuper.name»_downcast«eSub.name» «arg(eSuper.name)» (@allModelElements _ _ m).
		   
		   «ENDIF»«ENDFOR»

		«ENDFOR»
		
		«FOR eClass : ePackage.EClassifiers.filter(typeof(EClass))»
 			«FOR eReference : eClass.EReferences
 			»Fixpoint «eClass.name»_get«eReference.name.toFirstUpper»OnLinks («arg(eClass.name)» : «eClass.name») (l : list «mm_elink») : option («ReferenceType2Coq(eReference)») :=
 			match l with
 			| (Build_«mm_elink» «eClass.name»«eReference.name.toFirstUpper»«Keywords.PostfixEReference» (Build«eClass.name»«eReference.name.toFirstUpper» «eClass.name»_ctr «eReference.name»_ctr)) :: l' => 
 				  if beq_«eClass.name» «eClass.name»_ctr «arg(eClass.name)» then Some «eReference.name»_ctr else «eClass.name»_get«eReference.name.toFirstUpper»OnLinks «arg(eClass.name)» l'
 			| _ :: l' => «eClass.name»_get«eReference.name.toFirstUpper»OnLinks «arg(eClass.name)» l'
 			| nil => None
 			end.
 			
 			Definition «eClass.name»_get«eReference.name.toFirstUpper» («arg(eClass.name)» : «eClass.name») (m : «ePackage.name»Model) : option («ReferenceType2Coq(eReference)») :=
 			  «eClass.name»_get«eReference.name.toFirstUpper»OnLinks «arg(eClass.name)» (@allModelLinks _ _ m).
			«ENDFOR»

		«ENDFOR»
		
		Definition «mm»_defaultInstanceOfEClass («mm_eclass_qarg»: «mm_eclass») : («mm»_getTypeByEClass «mm_eclass_qarg») :=
		  match «mm_eclass_qarg» with
		  «FOR eClass : ePackage.EClassifiers.filter(typeof(EClass))»
		   | «eClass.name»«Keywords.PostfixEClass» => 
		   «EMFUtil.PrintDefaultValue(eClass)»
		  «ENDFOR»
		  end.
		
		(* Typeclass Instance *)
		Instance «mm» : Metamodel «mm_eobject» «mm_elink» «mm_eclass» «mm_eref» :=
		  {
		    denoteModelClass := «mm»_getTypeByEClass;
		    denoteModelReference := «mm»_getTypeByEReference;
		    toModelClass := «mm»_toEClass;
		    toModelReference := «mm»_toEReference;
		    toModelElement := «mm»_toEObjectOfEClass;
		    toModelLink := «mm»_toELinkOfEReference;
		    bottomModelClass := «mm»_defaultInstanceOfEClass;
		
		    (* Theorems *)
		    eqModelClass_dec := «mm»_eqEClass_dec;
		    eqModelReference_dec := «mm»_eqEReference_dec;
		
		    (* Constructors *)
		    BuildModelElement := Build_«mm_eobject»;
		    BuildModelLink := Build_«mm_elink»;
		  }.
		  
		(* Useful lemmas *)
		Lemma «ePackage.name»_invert : 
		  forall («mm_eclass_qarg»: «mm_eclass») (t1 t2: «mm»_getTypeByEClass «mm_eclass_qarg»), Build_«mm_eobject» «mm_eclass_qarg» t1 = Build_«mm_eobject» «mm_eclass_qarg» t2 -> t1 = t2.
		Proof.
		  intros.
		  inversion H.
		  apply inj_pair2_eq_dec in H1.
		  exact H1.
		  apply «mm»_eqEClass_dec.
		Qed.
	'''
	
	
	
	def static arg (String s) '''«s.split("_").map[s1 | if (s1.length()>1)  s1.toLowerCase.substring(0,2) else s1.toLowerCase.substring(0,1)].join»_arg'''
	def static arg1 (String s) '''«s.split("_").map[s1 |if (s1.length()>1)  s1.toLowerCase.substring(0,2) else s1.toLowerCase.substring(0,1)].join»_arg1'''
	def static arg2 (String s) '''«s.split("_").map[s1 | if (s1.length()>1)  s1.toLowerCase.substring(0,2) else s1.toLowerCase.substring(0,1)].join»_arg2'''
	
	def static AttributeType2Coq(EAttribute eAttribute)'''
	   «val eType = eAttribute.EType»
	   «IF eType.name == 'EInt'»nat«
		ELSEIF eType.name == 'EBoolean'»bool«
		ELSEIF eType.name == 'EString'»string«
		ELSEIF eType.name == 'Integer'»nat«
		ELSEIF eType.name == 'Boolean'»bool«
		ELSEIF eType.name == 'String'»string«
		ELSE»We don't know how to print «eType.name» «ENDIF
	»'''
	
	
	
	def static ReferenceType2Coq(EReference eReference)'''
	   «val eType = eReference.EType»
	   «IF eReference.upperBound == -1»list «eType.name»«
		ELSE»«eType.name»«ENDIF
	»'''
	
	def static  <T extends EObject> String PrintCtrArgsByPair(int size, String c){	
		if(size - 1 == 0){
			return '''«c»'''
		}else if(size - 1 == 1){
			return '''(fst «c») (snd «c»)'''
		}else{
			return String.format("%s %s", PrintCtrArgsByPair(size-1, '''(fst «c»)'''), '''(snd «c»)''')
		}
		
	}
	
}



/**
 * Removed
 * 
	get id of every eobject:
		Definition «mm»_getId («mm_eobject_qarg» : «mm_eobject») : nat :=
		  match «mm_eobject_qarg» with
		«FOR eClass : ePackage.EClassifiers.filter(typeof(EClass))»
		  | (Build_«mm_eobject» «eClass.name»EClass «mm_eobject_qarg») => «IF eClass.EAllAttributes.size > 0»«val fstAttr = eClass.EAllAttributes.get(0)»(get«eClass.name»«fstAttr.name.toFirstUpper» «mm_eobject_qarg») «ENDIF» 
  		«ENDFOR»
		  end.

    
		(** Helper of building EObject for model **)
		Definition «ePackage.name»«Keywords.PostfixMetamodel»_getEObjectFromEAttributeValues («farg_getEAttributeTypesByEClass» : «ePackage.name»«Keywords.PostfixMetamodel»_«Keywords.PostfixEClass») : («mm»_getEAttributeTypesByEClass «farg_getEAttributeTypesByEClass») -> «mm_eobject» :=
		  match «farg_getEAttributeTypesByEClass» with
		    «FOR eClass : ePackage.EClassifiers.filter(typeof(EClass))»
		    | «eClass.name»«Keywords.PostfixEClass» => 
		    «IF eClass.ESuperTypes.size > 0 »
		    	«IF eClass.EAttributes.size > 0»
		    	(fun («larg»: («eClass.ESuperTypes.get(0).name» * «FOR eAttributeCtr : eClass.EAttributes SEPARATOR " * "»«AttributeType2Coq(eAttributeCtr)»«ENDFOR»)) => (Build_«mm_eobject» «eClass.name»«Keywords.PostfixEClass» (Build«eClass.name» «PrintCtrArgsByPair(eClass.EAttributes.size+1, larg)»)))
		    	«ELSE»
		    	(fun («larg»: («eClass.ESuperTypes.get(0).name»)) => (Build_«mm_eobject» «eClass.name»«Keywords.PostfixEClass» (Build«eClass.name» «PrintCtrArgsByPair(1, larg)»)))
		    	«ENDIF»
		    «ELSE»
		    	«IF eClass.EAttributes.size > 0»
		    	(fun («larg»: («FOR eAttributeCtr : eClass.EAttributes SEPARATOR " * "»«AttributeType2Coq(eAttributeCtr)»«ENDFOR»)) => (Build_«mm_eobject» «eClass.name»«Keywords.PostfixEClass» (Build«eClass.name» «PrintCtrArgsByPair(eClass.EAttributes.size, larg)»)))
		    	«ELSE»
		    	(fun («larg»: Empty_set) => (Build_«mm_eobject» «eClass.name»«Keywords.PostfixEClass» (Build«eClass.name»)))
		    	«ENDIF»
		    «ENDIF»
			«ENDFOR»
		  end.
		
		(** Helper of building ELink for model **)
		Definition «ePackage.name»«Keywords.PostfixMetamodel»_getELinkFromERoleValues («farg_getERoleTypesByEReference» : «ePackage.name»«Keywords.PostfixMetamodel»_«Keywords.PostfixEReference») : («mm»_getERoleTypesByEReference «farg_getERoleTypesByEReference») -> «mm_elink» :=
		  match «farg_getERoleTypesByEReference» with
		    «FOR eClass : ePackage.EClassifiers.filter(typeof(EClass))»
				«FOR eReference : eClass.EReferences
		    	»| «eClass.name»«eReference.name.toFirstUpper»«Keywords.PostfixEReference» => (fun («larg»: («eClass.name» * «ReferenceType2Coq(eReference)»)) => (Build_«mm_elink» «eClass.name»«eReference.name.toFirstUpper»«Keywords.PostfixEReference» (Build«eClass.name»«eReference.name.toFirstUpper» «PrintCtrArgsByPair(2, larg)»)))
		    	«ENDFOR»
		    «ENDFOR»
		  end.
	eq check for super class:	
	
 */