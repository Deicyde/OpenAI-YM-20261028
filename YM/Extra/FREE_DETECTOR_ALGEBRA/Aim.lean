import YM.Extra.FREE_DETECTOR_ALGEBRA.CurlDetect
import YM.Extra.FREE_DETECTOR_ALGEBRA.Dialog

set_option warningAsError false

/-!
# One color tests on the jet variables

Taking real component or emitting along a color. No complex conjugated
DOFs; use multilinear extension or real parts separately. Used to show
rotational Gram on finite spaces usable for projecting color invariants,
and build actual invariant test label families for Ward kernel.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick  Labels
open scoped Topology BigOperators RealInnerProductSpace ContDiff

variable {G : Gauge} {x y : E4} {j k n : ℕ}

abbrev BareSol := Sol ℝ

def monochrome (v : G.Color) (j : ℕ) : BareSol j →ₗ[ℝ] Sol G.Color j := insertColor (tint (G:=G) v) j







def emits (P : BareSol j) : G.Color →ₗ[ℝ] Sol G.Color j where
  toFun v := monochrome v j P
  map_add' v w := by
    apply Subtype.ext; ext1 i; ext1 m; ext1 a
    exact smul_add (P.val i m a) v w
  map_smul' c v := by
    apply Subtype.ext; ext1 i; ext1 m; ext1 a
    exact smul_comm (P.val i m a) c v







/-- Aim takes the derivative coefficient *at opposite end* for emitted
probe. Extension independent; Taylor normalization both sides. -/
def aim (P : Sol G.Color j) (k : ℕ) (hx : x∈away) : Sol G.Color k :=
  (-1:ℝ)^k • ⟨_, (replied P).jets open_away hx⟩

theorem aim_read (P : Sol G.Color j) (Q : Sol G.Color k) (hx : x∈away) :
    dotF Q.val (aim (G:=G) P k hx).val = legKernel (G:=G) (dualSol _ _ P) (dualSol _ _ Q) x := by
  rw [replyTest P Q hx]
  change dotF _ ((-1:ℝ)^k • WaveOn.nth (reply (G:=G) P) k x) = _
  rw [map_smul,smul_eq_mul]

def targetAt (G : Gauge) (j k : ℕ) {x : E4} (hx : x∈away) : Sol G.Color j →ₗ[ℝ] Sol G.Color k where
  toFun p := aim p k hx
  map_add' p q := by
    apply (dualSol G.Color k).injective; apply LinearMap.ext; intro R
    have he (p : Sol G.Color j) : dualSol _ _ (aim (G:=G) p k hx) R = pairing (G:=G) hx (dualSol _ _ p) (dualSol _ _ R) := by
      rw [dualSol_val,dotF_symm,aim_read]; rfl
    simp only [map_add,LinearMap.add_apply,he]
  map_smul' c p := by
    apply (dualSol G.Color k).injective; apply LinearMap.ext; intro R
    have he (p : Sol G.Color j) : dualSol _ _ (aim (G:=G) p k hx) R = pairing (G:=G) hx (dualSol _ _ p) (dualSol _ _ R) := by
      rw [dualSol_val,dotF_symm,aim_read]; rfl
    simp only [map_smul,LinearMap.smul_apply,he]; rfl










end YM.Extra.FD
