import Lean.Data.HashMap
import Oml.Syntax

universe u v
variable {α : Type u} {β : Type v}

instance [BEq α] [Hashable α] [Repr α]: Repr (Lean.HashSet α) where
  reprPrec h n := h.toList.repr n

instance [BEq α] [Hashable α] [Lean.ToJson α]: Lean.ToJson (Lean.HashSet α) where
  toJson h := Lean.toJson h.toList
   
instance [BEq α] [Hashable α] [Lean.FromJson α]: Lean.FromJson (Lean.HashSet α) where
  fromJson?  
    | Lean.Json.arr as => 
      (as.mapM Lean.fromJson?).map fun a: Array α => 
        a.foldl Lean.HashSet.insert Lean.HashSet.empty
    | j => throw s!"expected JSON array, got '{j}'"
   
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
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

export REntityKind (rAspect rConcept rRelation)

instance : Hashable REntityKind where
  hash 
    | rAspect => 11
    | rConcept => 13
    | rRelation => 17

class REntity where
  kind: REntityKind
  name: String
  «prefix»: String
  deriving Hashable, BEq, Repr, Lean.FromJson, Lean.ToJson

inductive Exception where
  | error (message: String)
  deriving Repr, Lean.FromJson, Lean.ToJson

structure State where
  byPrefix : Lean.HashMap String Syntax.«Ontology» := .empty
  byNamespace : Lean.HashMap String Syntax.«Ontology» := .empty
  entities : Lean.HashSet REntity := .empty
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

def validateEntityDeclaration (p: String) (s: State) (vs: Syntax.VocabularyStatement): M State := do
  match vs with 
  | Syntax.VocabularyStatement.entity e =>
    let roe: Option REntity := match e with
      | Syntax.«Entity».«declaration» n (Syntax.«EntityKind».aspect _ _ _) => 
        some { kind := rAspect, name := n, «prefix» := p }
      | Syntax.«Entity».«declaration» n (Syntax.«EntityKind».concept _ _ _) => 
        some { kind := rConcept, name := n, «prefix» := p }
      | Syntax.«Entity».«declaration» n (Syntax.«EntityKind».relation _ _ _ _ _ _ _ _ _ _ _ _ _)=> 
        some { kind := rRelation, name := n, «prefix» := p }
      | _ =>
        none
    match roe with
      | some re =>
        match s.entities.contains re with
        | true =>
          throw (Exception.error s!"Error: duplicate entity declaration: {Lean.toJson re}")
        | false =>
          return { s with entities := s.entities.insert re }
      | none =>   
        return s
  | _ =>
    return s

def validateEntityDeclarationsOf (s: State) (v: Syntax.«Vocabulary»): M State := do
  match s.byPrefix.contains v.prefix with
  | true =>
    v.ownedStatements.foldlM (validateEntityDeclaration v.prefix) s
  | false =>
    pure s

def validateVocabularyEntityDeclarations: M State := do
  (← read).vocabularies.foldlM validateEntityDeclarationsOf (← get)

def validateVocabularyEntityDeclarations': M State := do
  let c: Context ← read
  validateVocabularyDeclarations >>= (fun s => c.vocabularies.foldlM validateEntityDeclarationsOf s)
  
end Resolver