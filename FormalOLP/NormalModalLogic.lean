import FormalOLP.NormalModalLogic.Syntax
import FormalOLP.NormalModalLogic.Semantics
import FormalOLP.NormalModalLogic.Soundness

/-!
# Normal modal logic

This topic follows the Open Logic Project's normal-modal-logic chapters.  The
syntax, relational models, and first soundness/frame-definability results are
kept in small native modules so later proof systems can build on them.

The relational definitions are adapted theorem-by-theorem from the modal
development in the pinned Lean Pool snapshot (`LeanPool/Incompleteness/
Foundation/Modal/Kripke/Basic.lean`, Pool revision
`c8ddda0a64f21cb019720cdda48c94354d4091e7`).  These declarations live in the
FormalOLP namespace and are independently proved for this scaffold.
-/
