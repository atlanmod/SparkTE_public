package fr.inria.atlanmod.coqtl.util

import org.eclipse.emf.ecore.EPackage
import org.eclipse.emf.ecore.resource.Resource
import org.eclipse.emf.ecore.xmi.impl.EcoreResourceFactoryImpl
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl
import org.eclipse.emf.ecore.resource.ResourceSet
import org.eclipse.emf.common.util.URI
import org.eclipse.emf.ecore.util.BasicExtendedMetaData
import org.eclipse.emf.ecore.util.ExtendedMetaData
import org.eclipse.emf.ecore.xmi.XMLResource
import org.eclipse.emf.ecore.EObject
import org.eclipse.emf.ecore.xmi.impl.XMIResourceFactoryImpl
import org.eclipse.emf.ecore.EClass
import org.eclipse.emf.ecore.EAttribute
import org.eclipse.emf.ecore.xmi.XMIResource

class EMFUtil {
	
	/** 
	 * @return the first epackage from the resource.
	 * */	
	def static getEPackage(Resource resource) {
		for (content : resource.contents) {
			if (content instanceof EPackage) {
				return content
			}
		}
	}
	
	/**
	 * load ecore in memory from {@code path}.
	 * @return resource set that have ecore metamodel loaded
	 * */
	def static loadEcore(URI path){
		Resource.Factory.Registry.INSTANCE.getExtensionToFactoryMap().put("ecore", new EcoreResourceFactoryImpl());
		Resource.Factory.Registry.INSTANCE.extensionToFactoryMap.put("xmi", new XMIResourceFactoryImpl());
		
		val ResourceSet rs = new ResourceSetImpl();
		val ExtendedMetaData extendedMetaData = new BasicExtendedMetaData(rs.getPackageRegistry());
		rs.getLoadOptions().put(XMLResource.OPTION_EXTENDED_META_DATA, extendedMetaData);


		val Resource r = rs.getResource(path, true);
		val EObject eObject = r.getContents().get(0);
		if (eObject instanceof EPackage) {
    		val EPackage p = eObject as EPackage;
    		rs.getPackageRegistry().put(p.getNsURI(), p);
    		return rs
		}else{
			throw new Exception("metamodel does not found at"+path)
		}
	}
	
	/**
	 * @return the default value of an {@code EAttribute}
	 * */
	def static PrintDefaultValue(EAttribute eAttribute) '''
		«val eType = eAttribute.EType»
		«IF eType.name == 'EInt' || eType.name == 'Integer'»0«
		ELSEIF eType.name == 'EBoolean' || eType.name == 'Boolean'»true«
		ELSEIF eType.name == 'EString' || eType.name == 'String'»""«
		ELSE»We don't know how to print «eType.name» «ENDIF
	»'''
	
	/**
	 * @return the default value of an {@code EClass}
	 * */
	def static String PrintDefaultValue(EClass eClass) '''
	«IF eClass.ESuperTypes.size > 0 »«
		IF eClass.EAttributes.size > 0»(Build«eClass.name» «EMFUtil.PrintDefaultValue(eClass.ESuperTypes.get(0))» "" «FOR eAttribute : eClass.EAttributes SEPARATOR " "»«EMFUtil.PrintDefaultValue(eAttribute)»«ENDFOR»)«
		ELSE»(Build«eClass.name» «EMFUtil.PrintDefaultValue(eClass.ESuperTypes.get(0))» "")«
		ENDIF»«
    ELSE»«
    	IF eClass.EAttributes.size > 0»(Build«eClass.name» "" «FOR eAttribute : eClass.EAttributes SEPARATOR " "»«EMFUtil.PrintDefaultValue(eAttribute)»«ENDFOR»)«
    	ELSE»(Build«eClass.name» "")«
    	ENDIF»«
    ENDIF»'''
    	
	
	/**
	 * @return the string represtation of an {@code o}
	 * */
	def static PrintValue(Object o) '''
		«IF o instanceof String»"«o.toString»"«
		ELSEIF o != null»«o.toString»«ELSE
		»""«ENDIF
	»'''
	
}
