-- PR #829 must-PASS: raw strings, char literals, primed and escaped identifiers holding comment
-- markers, with only honest code around them.
namespace LexFix.LegitRaw

def r1 : String := r"a -- b /- c"
def r2 : String := r#"say "/-" here"#
def q : Char := '"'
notation:max "qbpq" p'"''--" => p' ++ "!"
def «a--b» : Nat := 2

theorem honest : (1 : Nat) + 1 = 2 := rfl

end LexFix.LegitRaw
