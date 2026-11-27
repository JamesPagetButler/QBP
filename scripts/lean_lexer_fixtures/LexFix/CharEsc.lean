-- PR #829 Gemini r1 finding 3: every char-literal form Lean accepts, each followed by a string
-- holding a comment opener. All of it is code/strings to Lean, so `vac` is CODE.
namespace LexFix.CharEsc

def c1 : Char := '"'
def c2 : Char := '\"'
def c3 : Char := '\''
def c4 : Char := '\\'
def c5 : Char := '\x22'
def c6 : Char := '\u0022'
def c7 : Char := 'λ'
def s : String := "/-"

theorem vac : True := trivial

def close : String := "-/"

end LexFix.CharEsc
