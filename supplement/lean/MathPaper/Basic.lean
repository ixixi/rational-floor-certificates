import Std

/- Arithmetic parameters and checks. The main theorem is in MathPaper.Main. -/
namespace MathPaper

def numerator : Nat := 7
def denominator : Nat := 5
def modulus : Nat := 4290
def initialCells : Nat := 32
def refinementFactor : Nat := 4

theorem modulus_factorization : modulus = 2 * 3 * 5 * 11 * 13 := by decide

theorem base_is_reduced : Nat.gcd numerator denominator = 1 := by decide

theorem subdivision_endpoint : initialCells * refinementFactor ^ 3 = 2048 := by decide

end MathPaper
