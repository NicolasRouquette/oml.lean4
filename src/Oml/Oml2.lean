namespace Oml2

structure IdentifiedElement where

structure Ontology where 
  getPrefix: String
  getNamespace: String

structure Import where
  «namespace» : String

structure VocabularyImport extends Import where

structure VocabularyBox extends Ontology where

structure VocabularyStatement where

structure Axiom where

structure SpecializationAxiom extends Axiom where
  specializedTerm: SpecializableTerm

structure Vocabulary extends VocabularyBox where
  ownedImports: List VocabularyImport
  ownedStatements: List VocabularyStatement

structure Member extends IdentifiedElement where
  «name»: String

structure Term extends Member where

structure SpecializableTerm extends Term , VocabularyStatement where
  «ownedSpecializations»: List SpecializationAxiom

deriving instance Repr for Axiom
deriving instance Repr for IdentifiedElement
deriving instance Repr for Member
deriving instance Repr for Term
deriving instance Repr for Ontology
deriving instance Repr for Import
deriving instance Repr for VocabularyImport
deriving instance Repr for VocabularyBox
deriving instance Repr for VocabularyStatement
deriving instance Repr for Vocabulary
deriving instance Repr for SpecializableTerm
deriving instance Repr for SpecializationAxiom

end Oml2
