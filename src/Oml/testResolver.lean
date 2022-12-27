import Oml.Syntax
import Oml.Resolver
import Oml.testSyntax

namespace testResolver

open Resolver

def s0 : State := {}

def c0 : Context := { vocabularies := [testSyntax.rdfs] }
def c0': Context := { vocabularies := [testSyntax.rdfs, testSyntax.rdfs] }

def c1 : Context := { vocabularies := [testSyntax.rdfs, testSyntax.xsd, testSyntax.base, testSyntax.mission ] }
#eval c1

def r0 : EStateM.Result Exception State State := validateVocabularyDeclarations |>.run c0 |>.run s0
#eval r0

def r0': EStateM.Result Exception State State := validateVocabularyDeclarations |>.run c0' |>.run s0
#eval r0'

def r1 : EStateM.Result Exception State State := validateVocabularyDeclarations |>.run c1 |>.run s0
#eval r1

end testResolver
