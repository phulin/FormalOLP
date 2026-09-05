import FormalOLP
import TauCeti.Algebra.Algebra.Hom
import LeanPool.Computability
import LeanPool.FoZfc
import LeanPool.FormalizationOfBoundedArithmetic
import LeanPool.Incompleteness
import LeanPool.PartialCombinatoryAlgebras
import LeanPool.ZFLean
import LeanPool.Lean4GlCoalgebras
import LeanPool.LeanModelChecking
import LeanPool.Lentil

/-!
# FormalOLP and vendored Lean Pool aggregate boundary

This test imports every selected local Lean Pool entry alongside the public
FormalOLP root.  The entries are local source, not Lake dependencies; the
test is intentionally separate from the textbook-facing library target.
-/

#check FormalOLP.FirstOrderLogic.SemanticNotions.semantic_deduction_theorem
#check FirstOrder.ZFC.ModelZF
#check LeanPool.PartialCombinatoryAlgebras.PCA
