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
def r0 : EStateM.Result Exception State State := validateVocabularyDeclarations |>.run c0 |>.run s0
#eval r0

-- This detects a duplicate vocabulary declaration
def r0': EStateM.Result Exception State State := validateVocabularyDeclarations |>.run c0' |>.run s0
#eval r0'

-- This resolves all 4 vocabulary declarations
def r1a : EStateM.Result Exception State State := validateVocabularyDeclarations |>.run c1 |>.run s0
#eval r1a

def s1 : State := match r1a with | EStateM.Result.ok s _ => s | _ => {}
#eval s1

-- This resolves all vocabulary entity declarations from the state resulting from r1a.
def r1b : EStateM.Result Exception State State := validateVocabularyEntityDeclarations |>.run c1 |>.run s1
#eval r1b

-- This resolves all vocabulary declarations and their vocabulary entity declarations.
def r1b' : EStateM.Result Exception State State := validateVocabularyEntityDeclarations' |>.run c1 |>.run s0
#eval r1b'


end testResolver
