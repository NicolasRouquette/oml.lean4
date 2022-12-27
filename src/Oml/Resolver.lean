import Lean.Data.HashMap
import Oml.Syntax

universe u v
variable {α : Type u} {β : Type v}

instance [BEq α] [Hashable α] [Repr (α × β)]: Repr (Lean.HashMap α β) where
  reprPrec h n := h.toList.repr n

instance [BEq α] [Hashable α] [Lean.ToJson (α × β)]: Lean.ToJson (Lean.HashMap α β) where
  toJson h := Lean.toJson h.toList
   
instance [BEq α] [Hashable α] [Lean.FromJson (α × β)]: Lean.FromJson (Lean.HashMap α β) where
  fromJson?  
    | Lean.Json.arr as => 
      (as.mapM Lean.fromJson?).map fun a: Array (α × β) => Lean.HashMap.ofList (a.toList)
    | j => throw s!"expected JSON array, got '{j}'"
   
namespace Resolver

inductive REntityKind where
  | rAspect
  | rConcept
  | rRelation
  deriving Repr, Lean.FromJson, Lean.ToJson

class REntity where
  kind: REntityKind
  name: String
  vocabulary: String
  deriving Repr, Lean.FromJson, Lean.ToJson

inductive Exception where
  | error (message: String)
  deriving Repr, Lean.FromJson, Lean.ToJson

structure State where
  byPrefix : Lean.HashMap String Syntax.«Ontology» := .empty
  byNamespace : Lean.HashMap String Syntax.«Ontology» := .empty
  deriving Repr, Lean.FromJson, Lean.ToJson

structure Context where
  vocabularies: List Syntax.«Vocabulary» := .nil
  deriving Repr, Lean.FromJson, Lean.ToJson
  
-- The following 3 definitions are equivalent; the difference is purely syntactic.
abbrev MCore := EStateM Exception State
abbrev M     := ReaderT Context MCore
#print M

abbrev M'    := ReaderT Context <| MCore
#print M'

abbrev M''   := ReaderT Context <| ExceptT Exception <| StateM State
#print M''


def validateVocabularyDeclaration (s: State) (v: Syntax.«Vocabulary»): M State := do
  match (s.byPrefix.contains v.prefix, s.byNamespace.contains v.namespace) with
  | (false, false) =>
    pure { s with 
      byPrefix := s.byPrefix.insert v.prefix v.toOntology, 
      byNamespace := s.byNamespace.insert v.namespace v.toOntology }
  | (p, n) =>
    let pm := match p with 
      | true => s!"Error: multiple vocabularies with the same prefix: {v.prefix}"
      | false => ""
    let nm := match n with 
      | true => s!"Error: multiple vocabularies with the same namespace: {v.namespace}"
      | false => ""
    throw (Exception.error s!"{pm}\n{nm}")
  
def validateVocabularyDeclarations: M State := do
  (← read).vocabularies.foldlM validateVocabularyDeclaration (← get)

end Resolver