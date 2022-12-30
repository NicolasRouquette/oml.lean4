import Lean.Data.Json
import Oml.Instances

namespace Syntax

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

def «EntityKind».«propertyRestrictions» (e: «EntityKind»): List «PropertyRestrictionAxiom» :=
  match e with
  | .aspect p _ _ => p
  | .concept p _ _ => p
  | .relation _ _ _ _ _ _ _ _ _ _ p _ _ => p

def «EntityKind».«relationRestrictions» (e: «EntityKind»): List «RelationRestrictionAxiom» :=
  match e with
  | .aspect _ r _ => r
  | .concept _ r _ => r
  | .relation _ _ _ _ _ _ _ _ _ _ _ r _ => r

def «EntityKind».«specializations» (e: «EntityKind»): List «AbbrevIRI» :=
  match e with
  | .aspect _ _ s => s
  | .concept _ _ s => s
  | .relation _ _ _ _ _ _ _ _ _ _ _ _ s => s

export «EntityKind» (aspect concept relation)

inductive «Entity» where
 | «declaration» («name»: String) («kind»: «EntityKind»)
 | «reference» («abbrevIRI»: «AbbrevIRI») («kind»: «EntityKind»)
  deriving Repr, Lean.FromJson, Lean.ToJson
  
def «Entity».«propertyRestrictions» (e: «Entity»): List «PropertyRestrictionAxiom» :=
  match e with
  | .«declaration» _ k  => k.«propertyRestrictions»
  | .«reference» _ k    => k.«propertyRestrictions»
    
def «Entity».«relationRestrictions» (e: «Entity»): List «RelationRestrictionAxiom» :=
  match e with
  | .«declaration» _ k  => k.«relationRestrictions»
  | .«reference» _ k    => k.«relationRestrictions»

def «Entity».«specializations» (e: «Entity»): List «AbbrevIRI» :=
  match e with
  | .«declaration» _ k  => k.«specializations»
  | .«reference» _ k    => k.«specializations»

export «Entity» («declaration» «reference»)

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
    («specialization»: Option «AbbrevIRI» := none)
  | enumerated
    («literals»: List «Literal» := List.nil)
    («specialization»: Option «AbbrevIRI» := none)
  deriving Repr, Lean.FromJson, Lean.ToJson

def «ScalarKind».«specialization» (sk: «ScalarKind»): Option «AbbrevIRI» := 
  match sk with
  | .faceted _ _ _ _ _ _ _ _ _ s  => s
  | .enumerated _ s               => s

inductive «Scalar» where
 | «declaration» («name»: String) («kind»: «ScalarKind»)
 | «reference» («abbrevIRI»: «AbbrevIRI») («kind»: «ScalarKind»)
  deriving Repr, Lean.FromJson, Lean.ToJson

def «Scalar».«specialization» (sc: «Scalar»): Option «AbbrevIRI» :=
  match sc with
  | .«declaration» _ sk => sk.«specialization»
  | .«reference» _ sk   => sk.«specialization»
  
inductive «Structure» where
 | «declaration»
    («name»: String) 
    («propertyRestrictions» : List «PropertyRestrictionAxiom» := List.nil)
    («specializations»: List «AbbrevIRI» := List.nil)
 | «reference» 
    («abbrevIRI»: «AbbrevIRI»)
    («propertyRestrictions» : List «PropertyRestrictionAxiom» := List.nil)
    («specializations»: List «AbbrevIRI» := List.nil)
  deriving Repr, Lean.FromJson, Lean.ToJson

def «Structure».«propertyRestrictions» (s: «Structure»): List «PropertyRestrictionAxiom» :=
  match s with
  | .«declaration» _ p _  => p
  | .«reference» _ p _    => p

def «Structure».«specializations» (s: «Structure»): List «AbbrevIRI» :=
  match s with
  | .«declaration» _ _ s  => s
  | .«reference» _ _ s    => s

inductive «SemanticPropertyKind» where
  | scalar
    («specializations»: List «AbbrevIRI» := List.nil)
  | structured
    («specializations»: List «AbbrevIRI» := List.nil)
  deriving Repr, Lean.FromJson, Lean.ToJson

def «SemanticPropertyKind».«specializations» (spk: «SemanticPropertyKind»): List «AbbrevIRI» :=
  match spk with
  | .scalar s     => s
  | .structured s => s

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


def «SemanticProperty».«kind» (sp: «SemanticProperty»): «SemanticPropertyKind» :=
  match sp with
  | .«declaration» spk _ _ _ _  => spk
  | .«reference» spk _          => spk

def «SemanticProperty».«specializations» (sp: «SemanticProperty»): List «AbbrevIRI» :=
  sp.«kind».«specializations»

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
  «name»: String
  «antecedents»: List «Predicate»
  «consequents»: List «Predicate»
  deriving Repr, Lean.FromJson, Lean.ToJson
  
inductive «VocabularyStatement» where
  | «rule» (r: «Rule»)
  | «entity» (e: «Entity»)
  | «scalar» (s: «Scalar»)
  | «structure» (s: «Structure»)
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