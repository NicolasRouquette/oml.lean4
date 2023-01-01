import Lean.Data.HashMap
import Lean.Data.HashSet

instance [BEq α] [Hashable α] [Repr α]: Repr (Lean.HashSet α) where
  reprPrec h n := h.toList.repr n

instance [BEq α] [Hashable α] [Repr (α × β)]: Repr (Lean.HashMap α β) where
  reprPrec h n := h.toList.repr n

namespace MWE1

inductive «Entity» where
  | aspect
    (name: String)
    («specializations»: List String := List.nil)
  | concept
    (name: String)
    («specializations»: List String := List.nil)
  deriving Repr

def «Entity».name (e: «Entity»): String :=
  match e with
  | .aspect n _ => n
  | .concept n _ => n

def «Entity».«specializations» (e: «Entity»): List String :=
  match e with
  | .aspect _ s => s
  | .concept _ s => s

class «Vocabulary»where
  «ownedStatements»: List «Entity»
  deriving Repr

def v : «Vocabulary» := {
  ownedStatements := [
    «Entity».aspect "base:Container",
    «Entity».concept "mission:Component" [ "base:Container" ]
  ]
}

inductive RDeclarationKind where
  | rAspect
  | rConcept
  deriving BEq, Repr

def «Entity».toKind (e: «Entity»): RDeclarationKind :=
  match e with
  | .aspect _ _   => .rAspect
  | .concept _ _  => .rConcept

inductive Exception where
  | error (message: String)
  deriving Repr

abbrev Names := Lean.HashSet String
abbrev Name2NamesMap := Lean.HashMap String Names

structure State where
  declarations : Lean.HashMap String RDeclarationKind := .empty
  aspectSpecializations : Name2NamesMap := .empty
  conceptSpecializations : Name2NamesMap := .empty
  deriving Repr

structure Context where
  vocabularies: List «Vocabulary» := .nil
  deriving Repr

abbrev MCore := EStateM Exception State
abbrev M     := ReaderT Context MCore

def EStateM.Result.getState (r: EStateM.Result Exception State α): State :=
  match r with
  | EStateM.Result.ok _ s => s 
  | _ => {}

def State.appendSpecializations
  (d: String) (dts: List RDeclarationKind)
  (ds: List String)
  (coll: State → Name2NamesMap)
  (update: State → String → Names → State)
  : M Unit := do
  let s ← get
  match s.declarations.find? d with
  | some k =>
    if dts.contains k then
      let rds : Names := (coll s).findD d .empty
      let merged : Names := ds.foldl .insert rds
      let s' : State := update s d merged
      set s'
      pure ()
    else
      throw (Exception.error s!"Error: appendSpecializations: {repr d} is registered as a {repr k}, not one of {repr dts}.")
  | none =>
    throw (Exception.error s!"Error: appendSpecializations: there is no registered {repr dts}: {repr d} to append specializations to.")

def State.updateAspectSpecializations (s: State) (d: String) (ds: Names): State :=
  { s with aspectSpecializations := s.aspectSpecializations.insert d ds }

def State.appendAspectSpecializations (a: String) (as: List String): M Unit := do
  appendSpecializations a [ .rAspect ] as State.aspectSpecializations State.updateAspectSpecializations

def State.updateConceptSpecializations (s: State) (d: String) (ds: Names): State :=
  { s with conceptSpecializations := s.conceptSpecializations.insert d ds }

def State.appendConceptSpecializations (c: String) (cs: List String): M Unit := do
  appendSpecializations c [ .rAspect, .rConcept ] cs State.conceptSpecializations State.updateConceptSpecializations

def validateStatementDeclaration (e: «Entity»): M Unit := do
  let s ← get
  match s.declarations.find? e.name with
  | some ek =>
    throw (Exception.error s!"Error: declaration conflict: {repr e} is already registered as a {repr ek}.")
  | none =>
    let s := { s with declarations := s.declarations.insert e.name e.toKind }
    set s
    pure ()

def validateVocabularyStatementDeclarations: M Unit := do
  for v in (← read).vocabularies do
    for e in v.ownedStatements do
      validateStatementDeclaration e

def validateVocabularySpecialization (e: «Entity»): M Unit := do
  let s ← get
  match s.declarations.find? e.name with 
  | some ek =>
    if ek == e.toKind then
      match ek with
      | .rAspect =>
        State.appendAspectSpecializations e.name e.specializations
      | .rConcept =>
        State.appendConceptSpecializations e.name e.specializations
    else
      throw (Exception.error s!"Error: declaration inconsistency: {repr e} is registered as a {repr ek}, not a {repr e.toKind}.")
  | none =>
    pure ()
  
def validateVocabularySpecializations: M Unit := do
  for v in (← read).vocabularies do
    for e in v.ownedStatements do
      validateVocabularySpecialization e

def c0 : Context := { vocabularies := [v] }

def s0 : State := {}

def s1 : State := EStateM.Result.getState (validateVocabularyStatementDeclarations |>.run c0 |>.run s0)
#eval s1
-- { declarations := [("base:Container", MWE.RDeclarationKind.rAspect),
--                    ("mission:Component", MWE.RDeclarationKind.rConcept)],
--   aspectSpecializations := [],
--   conceptSpecializations := [] }


def s2 : State := EStateM.Result.getState (validateVocabularySpecializations |>.run c0 |>.run s1)
#eval s2
-- { declarations := [("base:Container", MWE.RDeclarationKind.rAspect),
--                    ("mission:Component", MWE.RDeclarationKind.rConcept)],
--   aspectSpecializations := [("base:Container", [])],
--   conceptSpecializations := [("mission:Component", ["base:Container"])] }

-- All keys of the aspectSpecialization map must have a corresponding declaration as an rAspect
theorem AllAspectsSpecializationsKeysAreDeclared (s: State): 
  ∀ a: String, s.aspectSpecializations.contains a → s.declarations.find? a == some .rAspect 
:= by
    sorry

-- All values of the aspectSpecialization map must have a corresponding declaration as an rAspect
theorem AllAspectsSpecializationsValuesAreDeclared (s: State) : 
  ∀ (a: String) (sup : String), (s.aspectSpecializations.findD a .empty).contains sup → s.declarations.find? sup == some .rAspect
:= by
    sorry

-- All keys of the conceptSpecializations map must have a corresponding declaration as an rConcept
theorem AllConceptSpecializationsKeysAreDeclared (s: State): 
  ∀ a: String, s.conceptSpecializations.contains a → s.declarations.find? a == some .rConcept
:= by
    sorry

-- All values of the conceptSpecializations map must have a corresponding declaration as an rAspect or rConcept
theorem AllConceptSpecializationsValuesAreDeclared (s: State) : 
  ∀ (a: String) (sup : String), (s.conceptSpecializations.findD a .empty).contains sup → 
    s.declarations.find? sup == some .rAspect || s.declarations.find? sup == some .rConcept 
:= by
    sorry
end MWE1