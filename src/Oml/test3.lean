import Oml.Oml3

/-- This is a subset of https://github.com/opencaesar/imce-vocabularies -/
namespace test3

open Oml3

def rdfs : «Vocabulary» := {
  «namespace» := "http://www.w3.org/2000/01/rdf-schema#"
  «prefix» := "rdfs"
  ownedStatements := [
    VocabularyStatement.scalar (Scalar.declaration "Literal" (ScalarKind.faceted))
  ]
}

def xsd : «Vocabulary» := {
  «namespace» := "http://www.w3.org/2001/XMLSchema#"
  «prefix» := "xsd"
  ownedStatements := [
    VocabularyStatement.scalar (Scalar.declaration "string" (ScalarKind.faceted («specializations» := [ (some "rdfs", "Literal")])))
  ]
}

def base : «Vocabulary» := {
  «namespace» := "http://imce.jpl.nasa.gov/foundation/base#"
  «prefix» := "base"
  ownedStatements := [
    VocabularyStatement.entity (Entity.declaration "IdentifiedElement" EntityKind.aspect),
    VocabularyStatement.entity (Entity.declaration "AggregatedElement" EntityKind.aspect),
    VocabularyStatement.entity (Entity.declaration "Container" EntityKind.aspect),
    VocabularyStatement.entity (Entity.declaration "ContainedElement" EntityKind.aspect),
    VocabularyStatement.entity (Entity.declaration "Contains" 
      (EntityKind.relation 
        («source» :=(none, "Container")) 
        («target» := (none, "ContainedElement"))
        («forward» := some "contains")
        («reverse» := some "isContainedIn")
        («inverseFunctional» := true)
        («asymmetric» := true)
        («irreflexive» := true)
      )),
    VocabularyStatement.entity (Entity.declaration "Aggregates" 
      (EntityKind.relation 
        («source» :=(none, "AggregatedElement")) 
        («target» := (none, "AggregatedElement"))
        («forward» := some "aggregates")
        («reverse» := some "isAggregatedIn")
        («asymmetric» := true)
        («irreflexive» := true)
      )),
    VocabularyStatement.semanticProperty 
      (SemanticProperty.declaration SemanticPropertyKind.scalar "hasIdentifier" (none, "IdentifiedElement") (some "xsd", "string"))
  ]
}


def mission : «Vocabulary» := {
  «namespace» := "http://imce.jpl.nasa.gov/foundation/mission#"
  «prefix» := "mission"
  ownedStatements := [
    VocabularyStatement.entity (Entity.declaration "PerformingElement" EntityKind.aspect),
    VocabularyStatement.entity (Entity.declaration "PresentingElement" EntityKind.aspect),
    VocabularyStatement.entity (Entity.declaration "SpecifiedElement" EntityKind.aspect),
    VocabularyStatement.entity (Entity.declaration "TraversingElement" EntityKind.aspect),
    VocabularyStatement.entity 
    (Entity.declaration "Component" 
      (EntityKind.concept
        («specializations» := [ 
          (some "base", "AggregatedElement"),
          (some "base", "ContainedElement"),
          (some "base", "Container"),
          (some "base", "IdentifiedElement"),
          (none, "PerformingElement"), 
          (none, "PresentingElement"), 
          (none, "SpecifiedElement") ])
        («relationRestrictions» := [
          (RelationRestrictionAxiom.range RangeRestrictionKind.all (some "base", "aggregates") (none, "Component")),
          (RelationRestrictionAxiom.range RangeRestrictionKind.all (some "base", "isAggregatedIn") (none, "Component")),
          (RelationRestrictionAxiom.range RangeRestrictionKind.all (some "base", "contains") (none, "Component")),
          (RelationRestrictionAxiom.range RangeRestrictionKind.all (some "base", "isContainedIn") (none, "Component"))
        ])))
  ]
}

#eval rdfs
#eval xsd
#eval base
#eval mission


end test3
