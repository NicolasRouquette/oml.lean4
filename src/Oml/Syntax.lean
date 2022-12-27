import Lean.Data.Json

namespace Syntax

instance : Lean.ToJson UInt8 := ⟨fun n => Lean.Json.num n.val⟩

instance : Lean.FromJson UInt8 := ⟨fun j => match Lean.Json.getInt? j with
| Except.error e => 
  throw e
| Except.ok i => 
  if h : i.toNat < UInt8.size then 
    return UInt8.ofNatCore i.toNat h 
  else 
    throw "Natural number less than 256 expected"⟩

instance : Lean.ToJson UInt32 := ⟨fun n => Lean.Json.num n.val⟩

instance : Lean.FromJson UInt32 := ⟨fun j => match Lean.Json.getInt? j with
| Except.error e => 
  throw e
| Except.ok i => 
  if h : i.toNat < UInt32.size then 
    return UInt32.ofNatCore i.toNat h 
  else 
    throw "Natural number less than 256 expected"⟩

structure «Ontology» where
  «namespace» : String
  «prefix»: String
  deriving Hashable, Repr, Lean.FromJson, Lean.ToJson

abbrev «AbbrevIRI» := (Option String) × String

inductive «Literal» where
  | booleanLiteral 
    («value»: Bool)
  | decimalLiteral 
    («value»: Int)
  | integerLiteral 
    («value»: Int)
  | doubleLiteral 
    («value»: Float)
  | quotedLiteral 
    («value»: String)
    («langTag»: Option String := none)
    («type»: Option «AbbrevIRI» := none)
  deriving Repr, Lean.FromJson, Lean.ToJson
  
inductive «VocabularyImportKind» where
  | vocabularyExtension
  | vocabularyUsage
  deriving Repr, Lean.FromJson, Lean.ToJson
  
class «VocabularyImport» where
  «kind» : «VocabularyImportKind»
  «importingPrefix»: String
  «importedPrefix»: String
  deriving Repr, Lean.FromJson, Lean.ToJson

inductive «CardinalityRestrictionKind» where
  | exactly
  | min
  | max
  deriving Repr, Lean.FromJson, Lean.ToJson

inductive «RangeRestrictionKind» where
  | all
  | some
  deriving Repr, Lean.FromJson, Lean.ToJson

inductive «PropertyRestrictionAxiom» where
  | scalarPropertyCardinality
    («kind» : «CardinalityRestrictionKind»)
    («property» : «AbbrevIRI»)
    («cardinality» : UInt32 := 1)
  | scalarPropertyRange
    («kind» : «RangeRestrictionKind»)
    («property» : «AbbrevIRI»)
    («range» : «AbbrevIRI»)
  | scalarPropertyValue
    («property» : «AbbrevIRI»)
    («value» : «Literal»)
  | structuredPropertyCardinality
    («kind» : «CardinalityRestrictionKind»)
    («property» : «AbbrevIRI»)
    («cardinality» : UInt32 := 1)
  | structuredPropertyRange
    («kind» : «RangeRestrictionKind»)
    («property» : «AbbrevIRI»)
    («range» : «AbbrevIRI»)
  | structuredPropertyValue
    («property» : «AbbrevIRI»)
    («value» : «Literal»)
  deriving Repr, Lean.FromJson, Lean.ToJson

inductive «RelationRestrictionAxiom» where
  | range
    («kind» : «RangeRestrictionKind»)
    («relation» : «AbbrevIRI»)
    («range» : «AbbrevIRI»)
  | cardinality
    («kind» : «CardinalityRestrictionKind»)
    («relation» : «AbbrevIRI»)
    («cardinality» : UInt32 := 1)
  | target
    («relation» : «AbbrevIRI»)
    («targetInstance» : «AbbrevIRI»)
  deriving Repr, Lean.FromJson, Lean.ToJson

inductive «EntityKind» where
  | aspect
    («propertyRestrictions» : List «PropertyRestrictionAxiom» := List.nil)
    («relationRestrictions» : List «RelationRestrictionAxiom» := List.nil)
    («specializations»: List «AbbrevIRI» := List.nil)
  | concept
    («propertyRestrictions» : List «PropertyRestrictionAxiom» := List.nil)
    («relationRestrictions» : List «RelationRestrictionAxiom» := List.nil)
    («specializations»: List «AbbrevIRI» := List.nil)
  | relation 
    («source»: «AbbrevIRI»)
    («target»: «AbbrevIRI»)
    («forward»: Option String := none)
    («reverse»: Option String := none)
    («functional»: Bool := false) 
    («inverseFunctional»: Bool := false) 
    («asymmetric»: Bool := false)
    («reflexive»: Bool := false) 
    («irreflexive»: Bool := false) 
    («transitive»: Bool := false)
    («propertyRestrictions» : List «PropertyRestrictionAxiom» := List.nil)
    («relationRestrictions» : List «RelationRestrictionAxiom» := List.nil)
    («specializations»: List «AbbrevIRI» := List.nil)
  deriving Repr, Lean.FromJson, Lean.ToJson

inductive «Entity» where
 | «declaration» («name»: String) («kind»: «EntityKind»)
 | «reference» («abbrevIRI»: «AbbrevIRI») («kind»: «EntityKind»)
  deriving Repr, Lean.FromJson, Lean.ToJson
  
inductive «ScalarKind» where
  | faceted
    («length»: Option UInt8 := none)
    («minLength»: Option UInt8 := none)
    («maxLength»: Option UInt8 := none)
    («pattern»: Option String := none)
    («language»: Option String := none)
    («minInclusive»: Option «Literal» := none)
    («minExclusive»: Option «Literal» := none)
    («maxInclusive»: Option «Literal» := none)
    («maxExclusive»: Option «Literal» := none)
    («specializations»: List «AbbrevIRI» := List.nil)
  | enumerated
    («literals»: List «Literal» := List.nil)
    («specializations»: List «AbbrevIRI» := List.nil)
  deriving Repr, Lean.FromJson, Lean.ToJson

inductive «Scalar» where
 | «declaration» («name»: String) («kind»: «ScalarKind»)
 | «reference» («abbrevIRI»: «AbbrevIRI») («kind»: «ScalarKind»)
  deriving Repr, Lean.FromJson, Lean.ToJson

inductive «SemanticPropertyKind» where
  | scalar
    («specializations»: List «AbbrevIRI» := List.nil)
  | structured
    («specializations»: List «AbbrevIRI» := List.nil)
  deriving Repr, Lean.FromJson, Lean.ToJson

inductive «SemanticProperty» where
 | «declaration» 
    («kind»: «SemanticPropertyKind»)
    («name»: String)
    («domain»: «AbbrevIRI») 
    («range»: «AbbrevIRI») -- resolve to Scalar or Structure according to kind
    («functional»: Bool := false) 
 | «reference» 
    («kind»: «SemanticPropertyKind»)
    («abbrevIRI»: «AbbrevIRI») 
  deriving Repr, Lean.FromJson, Lean.ToJson

inductive «Predicate» where
  | «type» («variable»: String) («type»: «AbbrevIRI»)
  | «sameAsVariable» («variable1»: String) («variable2»: String) 
  | «sameAsInstance» («variable1»: String) («instance2»: «AbbrevIRI») 
  | «differentFromVariable» («variable1»: String) («variable2»: String) 
  | «differentFromInstance» («variable1»: String) («instance2»: «AbbrevIRI»)
  | «featureVariable» («variable1»: String) («variable2»: String)
  | «featureLiteral» («variable1»: String) («literal2»: «Literal»)
  | «featureInstance» («variable1»: String) («instance2»: «AbbrevIRI»)
  | «relationEntityVariable» («variable1»: String) («entityVariable»: String) («variable2»: String) 
  | «relationEntityInstance» («variable1»: String) («entityVariable»: String) («instance2»: «AbbrevIRI») 
  deriving Repr, Lean.FromJson, Lean.ToJson

class «Rule» where
  «antecedents»: List «Predicate»
  «consequents»: List «Predicate»
  deriving Repr, Lean.FromJson, Lean.ToJson
  
inductive «VocabularyStatement» where
  | «rule» (r: «Rule»)
  | «entity» (e: «Entity»)
  | «scalar» (s: «Scalar»)
  | «structure» 
    («name»: String)
    («propertyRestrictions» : List «PropertyRestrictionAxiom» := List.nil)
  | «annotationProperty» («name»: String)
  | «semanticProperty» (p: «SemanticProperty»)
  deriving Repr, Lean.FromJson, Lean.ToJson

class «Vocabulary» extends «Ontology» where
  «ownedImports»: List «VocabularyImport» := List.nil
  «ownedStatements»: List «VocabularyStatement» := List.nil
  deriving Repr, Lean.FromJson, Lean.ToJson

instance : Hashable «Vocabulary» where
  hash v := hash v.toOntology

inductive «VocabularyBundleImportKind» where
  | vocabularyBundleExtension
  | vocabularyBundleUsage
  deriving Repr, Lean.FromJson, Lean.ToJson
  
class «VocabularyBundleImport» where
  «kind» : «VocabularyBundleImportKind»
  «importingPrefix»: String
  «importedPrefix»: String
  deriving Repr, Lean.FromJson, Lean.ToJson

inductive «DescriptionImportKind» where
  | descriptionExtension
  | descriptionUsage
  deriving Repr, Lean.FromJson, Lean.ToJson
  
class «DescriptionImport» where
  «kind» : «DescriptionImportKind»
  «importingPrefix»: String
  «importedPrefix»: String
  deriving Repr, Lean.FromJson, Lean.ToJson

inductive «DescriptionBundleImportKind» where
  | descriptionBundleExtension
  | descriptionBundleInclusion
  | descriptionBundleUsage
  deriving Repr, Lean.FromJson, Lean.ToJson

class «DescriptionBundleImport» where
  «kind» : «DescriptionBundleImportKind»
  «importingPrefix»: String
  «importedPrefix»: String
  deriving Repr, Lean.FromJson, Lean.ToJson

end Syntax