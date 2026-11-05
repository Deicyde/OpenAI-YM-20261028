import YM.Paley.Line

/-!
# Limits on the closed upper half-plane
-/
set_option autoImplicit false
namespace YM.Paley
open Complex

lemma highC : IsClosed high := isClosed_le continuous_const continuous_im

end YM.Paley
