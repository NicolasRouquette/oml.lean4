
import Lean.Data.HashMap
import Oml.Instances
import Oml.Syntax

namespace Resolver

class RDeclaration where
  name: String
  «prefix»: String
  deriving Hashable, BEq, Repr, Lean.FromJson, Lean.ToJson

abbrev RDeclarations := Lean.HashSet RDeclaration

inductive RLiteral where
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
    («langTag»: Option String)
    («type»: RDeclaration)
  deriving Repr, Lean.FromJson, Lean.ToJson

inductive RDeclarationKind where
  | rAspect
  | rConcept
  | rRelation
  | rStructure
  | rFacetedScalar
    («length»: Option UInt8)
    («minLength»: Option UInt8)
    («maxLength»: Option UInt8)
    («pattern»: Option String)
    («language»: Option String)
  | rEnumeratedScalar
  | rAnnotationProperty
  | rScalarProperty
    («functional»: Bool) 
  | rStructuredProperty
    («functional»: Bool) 
  | rForwardProperty
  | rReverseProperty
  deriving Repr, Lean.FromJson, Lean.ToJson

inductive RDeclarationType where
  | Aspect
  | Concept
  | Relation
  | Structure
  | FacetedScalar
  | EnumeratedScalar
  | AnnotationProperty
  | ScalarProperty
  | StructuredProperty
  | ForwardProperty
  | ReverseProperty
  deriving BEq, Repr, Lean.FromJson, Lean.ToJson

def RDeclarationKind.type (rk: RDeclarationKind) : RDeclarationType :=
  match rk with
  | rAspect                   => RDeclarationType.Aspect
  | rConcept                  => RDeclarationType.Concept
  | rRelation                 => RDeclarationType.Relation
  | rStructure                => RDeclarationType.Structure
  | rFacetedScalar _ _ _ _ _  => RDeclarationType.FacetedScalar
  | rEnumeratedScalar         => RDeclarationType.EnumeratedScalar
  | rAnnotationProperty       => RDeclarationType.AnnotationProperty
  | rScalarProperty _         => RDeclarationType.ScalarProperty
  | rStructuredProperty _     => RDeclarationType.StructuredProperty
  | rForwardProperty          => RDeclarationType.ForwardProperty
  | rReverseProperty          => RDeclarationType.ReverseProperty

instance : BEq RDeclarationKind where beq := fun k1 k2 => k1.type == k2.type

inductive Exception where
  | error (message: String)
  deriving Repr, Lean.FromJson, Lean.ToJson

structure State where
  byPrefix : Lean.HashMap String Syntax.«Ontology» := .empty
  byNamespace : Lean.HashMap String Syntax.«Ontology» := .empty
  -- declaration axtioms for entities and properties
  declarations : Lean.HashMap RDeclaration RDeclarationKind := .empty
  -- specialization axioms
  scalarSpecializations : Lean.HashMap RDeclaration RDeclaration := .empty
  structureSpecializations : Lean.HashMap RDeclaration RDeclarations := .empty
  aspectSpecializations : Lean.HashMap RDeclaration RDeclarations := .empty
  conceptSpecializations : Lean.HashMap RDeclaration RDeclarations := .empty
  relationSpecializations : Lean.HashMap RDeclaration RDeclarations := .empty
  scalarPropertySpecializations : Lean.HashMap RDeclaration RDeclarations := .empty
  structuredPropertySpecializations : Lean.HashMap RDeclaration RDeclarations := .empty
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

def State.appendSpecializations
  (d: RDeclaration) (dts: List RDeclarationType)
  (ds: List RDeclaration)
  (coll: State → Lean.HashMap RDeclaration RDeclarations)
  (update: State → RDeclaration → RDeclarations → State)
  : M State := do
  let s ← get
  match s.declarations.find? d with
  | some k =>
    if dts.contains k.type then
      let rds := (coll s).findD d .empty
      let merged : RDeclarations := ds.foldl .insert rds
      let s' : State := update s d merged
      pure s'
    else
      throw (Exception.error s!"Error: appendSpecializations: {repr d} is registered as a {repr k.type}, not one of {repr dts}.")
  | none =>
    throw (Exception.error s!"Error: appendSpecializations: there is no registered {repr dts}: {repr d} to append specializations to.")

def State.updateAspectSpecializations (s: State) (d: RDeclaration) (ds: RDeclarations): State :=
  { s with aspectSpecializations := s.aspectSpecializations.insert d ds }

def State.updateConceptSpecializations (s: State) (d: RDeclaration) (ds: RDeclarations): State :=
  { s with conceptSpecializations := s.conceptSpecializations.insert d ds }

def State.updateRelationSpecializations (s: State) (d: RDeclaration) (ds: RDeclarations): State :=
{ s with relationSpecializations := s.relationSpecializations.insert d ds }

def State.updateStructureSpecializations (s: State) (d: RDeclaration) (ds: RDeclarations): State :=
{ s with structureSpecializations := s.structureSpecializations.insert d ds }

def State.updateScalarPropertySpecializations (s: State) (d: RDeclaration) (ds: RDeclarations): State :=
{ s with scalarPropertySpecializations := s.scalarPropertySpecializations.insert d ds }

def State.updateStructuredPropertySpecializations (s: State) (d: RDeclaration) (ds: RDeclarations): State :=
{ s with structuredPropertySpecializations := s.structuredPropertySpecializations.insert d ds }

def State.appendAspectSpecializations (a: RDeclaration) (as: List RDeclaration): M State := do
  appendSpecializations a [ .Aspect ] as State.aspectSpecializations State.updateAspectSpecializations

def State.appendConceptSpecializations (c: RDeclaration) (cs: List RDeclaration): M State := do
  appendSpecializations c [ .Aspect, .Concept ] cs State.conceptSpecializations State.updateConceptSpecializations

def State.appendRelationSpecializations (r: RDeclaration) (rs: List RDeclaration): M State := do
  appendSpecializations r [ .Aspect, .Relation ] rs State.relationSpecializations State.updateRelationSpecializations

def State.appendStructureSpecializations (s: RDeclaration) (ss: List RDeclaration): M State := do
  appendSpecializations s [ .Structure ] ss State.structureSpecializations State.updateStructureSpecializations

def State.appendScalarPropertySpecializations (s: RDeclaration) (ss: List RDeclaration): M State := do
  appendSpecializations s [ .ScalarProperty ] ss State.scalarPropertySpecializations State.updateScalarPropertySpecializations

def State.appendStructuredPropertySpecializations (s: RDeclaration) (ss: List RDeclaration): M State := do
  appendSpecializations s [ .StructuredProperty ] ss State.structuredPropertySpecializations State.updateStructuredPropertySpecializations

/-- The set of all vocabularies must have unique combinations of prefixes and namespaces. -/

def validateVocabularyDeclaration (s: State) (v: Syntax.«Vocabulary»): M State := do
  match (s.byPrefix.contains v.prefix, s.byNamespace.contains v.namespace) with
  | (false, false) =>
    pure { s with 
      byPrefix := s.byPrefix.insert v.prefix v.toOntology, 
      byNamespace := s.byNamespace.insert v.namespace v.toOntology }
  | (p, n) =>
    let pm := if p then s!"Error: multiple vocabularies with the same prefix: {v.prefix}" else ""
    let nm := if n then s!"Error: multiple vocabularies with the same namespace: {v.namespace}" else ""
    throw (Exception.error s!"{pm}\n{nm}")
  
def validateVocabularyDeclarations: M State := do
  (← read).vocabularies.foldlM validateVocabularyDeclaration (← get)

/-- Vocabulary statements must declare unique combinations of names within a given namespace prefix. -/

def validateStatementDeclaration (p: String) (s: State) (vs: Syntax.VocabularyStatement): M State := do
  match vs with 
  | .entity e =>
    let ((od: Option RDeclaration), (ok: Option RDeclarationKind), (of: Option String), (or: Option String)) := match e with
      | .«declaration» n (Syntax.«EntityKind».aspect _ _ _) => 
        (some (RDeclaration.mk (name := n) p), some RDeclarationKind.rAspect, none, none)
      | .«declaration» n (Syntax.«EntityKind».concept _ _ _) => 
        (some (RDeclaration.mk (name := n) («prefix» := p)), some RDeclarationKind.rConcept, none, none)
      | .«declaration» n (Syntax.«EntityKind».relation _ _ of or _ _ _ _ _ _ _ _ _) =>
        (some (RDeclaration.mk (name := n) («prefix» := p)), some RDeclarationKind.rRelation, of, or)
      | _ =>
        (none, none, none, none)
    match (od, ok) with
      | (some d, some k) =>
        match s.declarations.find? d with
        | some dk =>
          throw (Exception.error s!"Error: entity declaration: {Lean.toJson d} was resolved as a {Lean.toJson dk} but there is a conflicting or duplicate declaration as a {Lean.toJson k}.")
        | none =>
          let s := { s with declarations := s.declarations.insert d k }
          let s ← match of with
            | none => 
              pure s
            | some f =>
              let fd := RDeclaration.mk (name := f) («prefix» := p)
              match s.declarations.find? fd with
                | some fdk =>
                  throw (Exception.error s!"Error: entity declaration: {Lean.toJson fd} was resolved as a {Lean.toJson fdk} but there is a conflicting or duplicate declaration as a Forward Property.")
                | none =>
                  pure { s with declarations := s.declarations.insert fd RDeclarationKind.rForwardProperty }
          let s ← match or with
            | none => 
              pure s
            | some r =>
              let rd := RDeclaration.mk (name := r) («prefix» := p)
              match s.declarations.find? rd with
                | some rdk =>
                  throw (Exception.error s!"Error: entity declaration: {Lean.toJson rd} was resolved as a {Lean.toJson rdk} but there is a conflicting or duplicate declaration as a Reverse Property.")
                | none =>
                  pure { s with declarations := s.declarations.insert rd RDeclarationKind.rReverseProperty }                  
          return s
      | _ =>   
        return s
  | .scalar sc =>
    match sc with
      | .«declaration» n k =>
        let d := RDeclaration.mk (name := n) («prefix» := p)
        match s.declarations.find? d with
        | some dk =>
          throw (Exception.error s!"Error: entity declaration: {Lean.toJson d} was resolved as a {Lean.toJson dk} but there is a conflicting or duplicate declaration as a {Lean.toJson k}.")
        | none =>
          match k with
          | Syntax.«ScalarKind».faceted len minL maxL pat lang _ _ _ _ _ =>
            return { s with declarations := s.declarations.insert d (RDeclarationKind.rFacetedScalar len minL maxL pat lang) }
          | Syntax.«ScalarKind».enumerated _ _ =>
            return { s with declarations := s.declarations.insert d RDeclarationKind.rEnumeratedScalar }
      | _ =>
        return s
  | .structure st =>
    match st with
      | .«declaration» n _ =>
        let d := RDeclaration.mk (name := n) («prefix» := p)
        match s.declarations.find? d with
        | some dk =>
          throw (Exception.error s!"Error: entity declaration: {Lean.toJson d} was resolved as a {Lean.toJson dk} but there is a conflicting or duplicate declaration as a Structure.")
        | none =>
          return { s with declarations := s.declarations.insert d RDeclarationKind.rStructure }
      | _ =>
        return s
  | .annotationProperty ap =>
    let d := RDeclaration.mk (name := ap) («prefix» := p)
    match s.declarations.find? d with
      | some dk =>
        throw (Exception.error s!"Error: entity declaration: {Lean.toJson d} was resolved as a {Lean.toJson dk} but there is a conflicting or duplicate declaration as an AnnotationProperty.")
      | none =>
        return { s with declarations := s.declarations.insert d RDeclarationKind.rAnnotationProperty }
  | .semanticProperty sp =>
    match sp with
      | .«declaration» sk sn _ _ isFunc =>
        let d := RDeclaration.mk (name := sn) («prefix» := p)
        match sk with
          | .scalar _ =>
            match s.declarations.find? d with
              | some dk =>
                throw (Exception.error s!"Error: entity declaration: {Lean.toJson d} was resolved as a {Lean.toJson dk} but there is a conflicting or duplicate declaration as an ScalarProperty.")
              | none =>
                return { s with declarations := s.declarations.insert d (RDeclarationKind.rScalarProperty isFunc) }
          | .structured _ =>
            match s.declarations.find? d with
              | some dk =>
                throw (Exception.error s!"Error: entity declaration: {Lean.toJson d} was resolved as a {Lean.toJson dk} but there is a conflicting or duplicate declaration as an StructuredProperty.")
              | none =>
                return { s with declarations := s.declarations.insert d (RDeclarationKind.rStructuredProperty isFunc) }
      | _ =>
        return s
  | _ =>
    return s

def validateStatementDeclarationsIn (s: State) (v: Syntax.«Vocabulary»): M State := do
  if s.byPrefix.contains v.prefix then
    v.ownedStatements.foldlM (validateStatementDeclaration v.prefix) s
  else
    pure s

def validateVocabularyStatementDeclarations: M State := do
  (← read).vocabularies.foldlM validateStatementDeclarationsIn (← get)

def validateVocabularyStatementDeclarations': M State := do
  let c: Context ← read
  validateVocabularyDeclarations >>= (fun s => c.vocabularies.foldlM validateStatementDeclarationsIn s)

/-- Validation of specialization axioms -/
def abbrevDeclatation (p: String) (a: Syntax.AbbrevIRI): M RDeclaration := do
  match a with
  | (none, n) =>
    pure (RDeclaration.mk (name := n) («prefix» := p))
  | (some ap, n) =>
    let s: State ← get
    match s.byPrefix.contains ap with
    | true =>
      pure (RDeclaration.mk (name := n) («prefix» := ap))
    | false =>
      throw (Exception.error s!"Error: there is no registered vocabulary with prefix {ap} to resolve abbreviated IRI {a}.")

def resolveDeclaration (rd: RDeclaration): M (RDeclaration × RDeclarationKind) := do
  let s: State ← get
  match s.declarations.findEntry? rd with
  | some rdk =>
    pure rdk
  | none =>
    throw (Exception.error s!"Error: there is no registered declaration for entity: {rd.prefix}:{rd.name}.")

def resolveAbbrev (p: String) (a: Syntax.AbbrevIRI): M (RDeclaration × RDeclarationKind) := do
  let rd ← abbrevDeclatation p a
  resolveDeclaration rd

def resolveEntity (p: String) (e: Syntax.Entity): M (RDeclaration × RDeclarationKind) := do
  let rd: RDeclaration ← match e with
    | .declaration n _ => 
      pure (RDeclaration.mk (name := n) («prefix» := p))
    | .reference a _ =>
      abbrevDeclatation p a
  resolveDeclaration rd

def resolveEntityOfKind (p: String) (dts: List RDeclarationType) (rs: List RDeclaration) (ab: Syntax.AbbrevIRI): M (List RDeclaration) := do
  let ar ← resolveAbbrev p ab
  if dts.contains ar.snd.type then
    return rs.cons ar.fst
  else
    throw (Exception.error s!"Error: abbreviated IRI: {ab} resolves to a {repr ar.snd.type} instead of one of {repr dts}")

def resolveEntitiesOfKind (p: String) (dts: List RDeclarationType) (es : List Syntax.AbbrevIRI): M (List RDeclaration) := do
  es.foldlM (resolveEntityOfKind p dts) List.nil

def resolveStructure (p: String) (s: Syntax.Structure): M (RDeclaration × RDeclarationKind) := do
  let rd: RDeclaration ← match s with
    | .declaration n _ _ => 
      pure (RDeclaration.mk (name := n) («prefix» := p))
    | .reference a _ _ =>
      abbrevDeclatation p a
  let rs ← resolveDeclaration rd
  if rs.snd.type == RDeclarationType.Structure then
    pure rs
  else
    throw (Exception.error s!"Error: conflicting resolution for {repr rs.fst} as {repr rs.snd} vs. Structure.")

def resolveScalar (p: String) (s: Syntax.Scalar): M (RDeclaration × RDeclarationKind) := do
  let rd: RDeclaration ← match s with
    | .declaration n _ => 
      pure (RDeclaration.mk (name := n) («prefix» := p))
    | .reference a _ =>
      abbrevDeclatation p a
  let rs ← resolveDeclaration rd
  if rs.snd.type == RDeclarationType.FacetedScalar || rs.snd.type == RDeclarationType.EnumeratedScalar then
    pure rs
  else
    throw (Exception.error s!"Error: conflicting resolution for {repr rs.fst} as {repr rs.snd} vs. Scalar.")

def resolveSemanticProperty (p: String) (sp: Syntax.SemanticProperty): M (RDeclaration × RDeclarationKind) := do
  let rdsk ← match sp with
    | .declaration k n _ _ _ =>
      pure ((RDeclaration.mk (name := n) («prefix» := p)), k)
    | .reference k a =>
      let r ← abbrevDeclatation p a
      pure (r, k)
  let rs ← resolveDeclaration rdsk.fst
  match rdsk.snd with
  | .scalar _ =>
    if rs.snd.type == RDeclarationType.ScalarProperty then
      pure rs
    else
    throw (Exception.error s!"Error: conflicting resolution for {repr rs.fst} as {repr rs.snd} vs. ScalarProperty.")
  | .structured _ =>
    if rs.snd.type == RDeclarationType.StructuredProperty then
      pure rs
    else
    throw (Exception.error s!"Error: conflicting resolution for {repr rs.fst} as {repr rs.snd} vs. StructureProperty.")

def getCompatibleKinds (t: RDeclarationType): List RDeclarationType :=
  match t with
  | .Concept => [ .Aspect, .Concept ]
  | .Relation => [ .Aspect, .Relation ]
  | x => [ x ]

def validateVocabularySpecialization (p: String) (s: State) (vs: Syntax.VocabularyStatement): M State := do
  match vs with 
  | .entity e =>
    let rdk : RDeclaration × RDeclarationKind ← resolveEntity p e
    let es : List Syntax.AbbrevIRI := e.«specializations»
    let rs : List RDeclaration ← resolveEntitiesOfKind p (getCompatibleKinds rdk.snd.type) es -- TODO: For Concept, Relation, needs to allow for Aspect!
    match rdk.snd.type with
    | .Aspect =>
      State.appendAspectSpecializations rdk.fst rs
    | .Concept =>
      State.appendConceptSpecializations rdk.fst rs
    | .Relation =>
      State.appendRelationSpecializations rdk.fst rs
    | _ =>
      pure (← get)
  | .scalar sc =>
    let rdk : RDeclaration × RDeclarationKind ← resolveScalar p sc
    match sc.«specialization» with
    | none =>
      pure (← get)
    | some ab =>
      let s ← get
      let ar ← resolveAbbrev p ab
      if ar.snd == rdk.snd then
        match s.scalarSpecializations.find? rdk.fst with
        | none =>
          pure { s with scalarSpecializations := s.scalarSpecializations.insert rdk.fst ar.fst }
        | some ss =>
          if ss == ar.fst then
            pure s
          else
            throw (Exception.error s!"Error: conflicting specialization of Scalar: {repr rdk.fst} as {repr ss} vs. {repr ar.fst}.")
      else
        throw (Exception.error s!"Error: abbreviated IRI: {ab} resolves to a {repr ar.snd.type} instead of a Scalar.")
  | .structure st =>
    let rdk : RDeclaration × RDeclarationKind ← resolveStructure p st
    let ss : List Syntax.AbbrevIRI := st.«specializations»
    let rs : List RDeclaration ← resolveEntitiesOfKind p (getCompatibleKinds rdk.snd.type) ss
    State.appendStructureSpecializations rdk.fst rs
  | .semanticProperty sp =>
    let rdk : RDeclaration × RDeclarationKind ← resolveSemanticProperty p sp
    let ss : List Syntax.AbbrevIRI := sp.«specializations»
    let rs : List RDeclaration ← resolveEntitiesOfKind p (getCompatibleKinds rdk.snd.type) ss
    match sp.kind with
    | .scalar _ =>
      State.appendScalarPropertySpecializations rdk.fst rs
    | .structured _ =>
      State.appendStructuredPropertySpecializations rdk.fst rs
    pure (← get)
  | _ =>
    pure (← get)
  
def validateVocabularySpecializationsIn (s: State) (v: Syntax.«Vocabulary»): M State := do
  if s.byPrefix.contains v.prefix then
    v.ownedStatements.foldlM (validateVocabularySpecialization v.prefix) s
  else
    pure s

def validateVocabularySpecializations: M State := do
  (← read).vocabularies.foldlM validateVocabularySpecializationsIn (← get)
  
def validateVocabularySpecializations': M State := do
  let c: Context ← read
  validateVocabularyDeclarations 
  >>= (fun s => c.vocabularies.foldlM validateStatementDeclarationsIn s) >>= (fun s => c.vocabularies.foldlM validateVocabularySpecializationsIn s)
  


end Resolver