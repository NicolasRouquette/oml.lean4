namespace Oml1

structure Element where
  getOntology: Ontology

structure Annotation extends Element where 
  property: AnnotationProperty
  value: Literal

structure AnnotatedElement extends Element where
  ownedAnnotations: List Annotation

structure IdentifiedElement extends AnnotatedElement where
  getIri: String

structure Ontology where 
  getPrefix: String
  getNamespace: String

structure VocabularyBox extends Ontology

class Vocabulary extends VocabularyBox where
  ownedImports: List VocabularyImport
  ownedStatements: List VocabularyStatement

class VocabularyBundle extends VocabularyBox where
  ownedImports: List VocabularyBundleImport

structure DescriptionBox extends Ontology

class Description extends DescriptionBox where
  ownedImports: List DescriptionImport
  ownedStatements: List DescriptionStatement

class DescriptionBundle extends DescriptionBox where
  ownedImports: List DescriptionBundleImport

structure Statement extends Element

structure VocabularyStatement extends Statement where
  owningVocabulary: Vocabulary
  
structure DescriptionStatement extends Statement where
  owningDescription: Description

structure Import extends AnnotatedElement where
  _namespace: string
  _prefix: string

class VocabularyImport extends Import where
  owningVocabulary: Vocabulary

class VocabularyExtension extends VocabularyImport

class VocabularyUsage extends VocabularyImport

class VocabularyBundleImport extends Import where
  owningVocabularyBundle: VocabularyBundle

class VocabularyBundleExtension extends VocabularyBundleImport

class VocabularyBundleInclusion extends VocabularyBundleImport

structure DescriptionImport extends Import where
  owningDescription: Description

class DescriptionExtension extends DescriptionImport

class DescriptionUsage extends DescriptionImport

structure DescriptionBundleImport extends Import where 
  owningDescriptionBundle: DescriptionBundle

class DescriptionBundleExtension extends DescriptionBundleImport

class DescriptionBundleInclusion extends DescriptionBundleImport

class DescriptionBundleUsage extends DescriptionBundleImport

structure Member extends IdentifiedElement where
  name: String
  getAbbreviatedIri: String

structure Term extends Member

structure SpecializableTerm extends Term, VocabularyStatement where
  ownedSpecializations: List SpecializationAxiom

structure _Type extends SpecializableTerm

structure Classifier extends _Type where
  ownedPropertyRestrictions: List PropertyRestrictionAxiom

structure Entity extends Classifier where
  ownedKeys: List KeyAxiom

class Aspect extends Entity

class Concept extends Entity where
  enumeratedInstances: List ConceptInstance

class RelationEntity extends Entity where
  source: Entity
  target: Entity
  forwardRelation: ForwardRelation
  reverseRelation: ReverseRelation
  functional: Boolean
  inverseFunctional: Boolean
  symmetric: Boolean
  asymmetric: Boolean
  reflexive: Boolean
  irreflexive: Boolean
  transitive: Boolean

structure Structure extends Classifier

structure Feature extends Term

structure Property extends Feature

structure AnnotationProperty extends Property, SpecializableTerm

structure SemanticProperty extends Property where
  isFunctional: Boolean
  getDomain: Classifier
  getRange: _Type

class ScalarProperty extends SemanticProperty, SpecializableTerm 

class StructuredProperty extends SemanticProperty, SpecializableTerm

structure Scalar extends _Type

structure Relation extends Feature 

class ForwardRelation extends Relation

class ReverseRelation extends Relation

class Rule extends Member, VocabularyStatement

structure Instance extends Element

class StructureInstance extends Instance

structure NamedInstance extends Member, Instance, DescriptionStatement

class ConceptInstance extends NamedInstance

class RelationInstance extends NamedInstance

structure Reference extends Element

structure SpecializableTermReference extends Reference , VocabularyStatement

structure ClassifierReference extends SpecializableTermReference

structure EntityReference extends ClassifierReference where
  ownedRelationRestrictions: List RelationRestrictionAxiom
  ownedKeys: List KeyAxiom

class AspectReference extends EntityReference where
  aspect: Aspect

class ConceptReference extends EntityReference where
  concept: Concept

class RelationEntityReference extends EntityReference where
  entity: RelationEntity

class StructureReference extends ClassifierReference where
  _structure: Structure

class AnnotationPropertyReference extends SpecializableTermReference where
  property: AnnotationProperty

class ScalarPropertyReference extends SpecializableTermReference where
  property: ScalarProperty

class StructuredPropertyReference extends SpecializableTermReference where
  property: StructuredProperty

class RelationReference extends Reference , VocabularyStatement where 
  relation: Relation

class RuleReference extends Reference , VocabularyStatement where
  rule: Rule

structure NamedInstanceReference extends Reference , DescriptionStatement  where
  ownedPropertyValues: List PropertyValueAssertion
  ownedLinks: List LinkAssertion

class ConceptInstanceReference extends NamedInstanceReference where
  _instance: ConceptInstance
  ownedTypes: List ConceptTypeAssertion

class RelationInstanceReference extends NamedInstanceReference where
  _instance: RelationInstance
  ownedTypes: List RelationTypeAssertion

structure Axiom extends Element

class SpecializationAxiom extends Axiom where
  specializedTerm: SpecializableTerm
  owningTerm: SpecializableTerm
  owningReference: SpecializableTermReference

structure RestrictionAxiom extends Axiom


end Oml1