import Oml.Syntax
import Oml.Resolver
import Oml.testSyntax

namespace testResolver

open Resolver

def s0 : State := {}

def c0 : Context := { vocabularies := [testSyntax.rdfs] }
def c0': Context := { vocabularies := [testSyntax.rdfs, testSyntax.rdfs] }

def c1 : Context := { vocabularies := [testSyntax.rdfs, testSyntax.xsd, testSyntax.base, testSyntax.mission ] }

-- This resolves a single vocabulary declaration.
def r0 : EStateM.Result Exception State Unit := validateVocabularyDeclarations |>.run c0 |>.run s0
#eval r0

-- This detects a duplicate vocabulary declaration
def r0': EStateM.Result Exception State Unit := validateVocabularyDeclarations |>.run c0' |>.run s0
#eval r0'

-- This resolves all 4 vocabulary declarations
def r1a : EStateM.Result Exception State Unit := validateVocabularyDeclarations |>.run c1 |>.run s0
#eval r1a

def s1 : State := EStateM.Result.getState r1a
#eval s1

-- This resolves all vocabulary entity declarations from the state resulting from r1a.
def r1b : EStateM.Result Exception State Unit := validateVocabularyStatementDeclarations |>.run c1 |>.run s1
#eval r1b

-- This resolves all vocabulary declarations and their vocabulary entity declarations.
def r1b' : EStateM.Result Exception State Unit := validateVocabularyStatementDeclarations' |>.run c1 |>.run s0
#eval r1b'

def s2 : State := EStateM.Result.getState r1b'
#eval s2

-- This resolves all vocabulary declarations, their vocabulary entity declarations and their specializations.
def r1c' : EStateM.Result Exception State Unit := validateVocabularySpecializations' |>.run c1 |>.run s0
#eval r1c'

def s1c' : State := EStateM.Result.getState r1c'
#eval s1c'

def r1c'': EStateM.Result Exception State Unit := validateVocabularySpecializations'' |>.run c1 |>.run s0
#eval r1c''

def s1c'' : State := EStateM.Result.getState r1c''
#eval s1c''


end testResolver
