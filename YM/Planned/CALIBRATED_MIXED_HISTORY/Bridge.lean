import YM.Extra.MULTISOURCE_TRAJECTORIES.Price
import YM.Next.MULTISOURCE.Curves
import YM.Planned.CALIBRATED_MIXED_HISTORY.Crude
import YM.Planned.CALIBRATED_MIXED_HISTORY.Purse
import YM.Push.ABSOLUTE_SUMS.Footprint
import YM.Push.RELAY_DIFFERENCE.TwoSided


/-!
# A class of irreducible mixed value tests automatic by geometric trade at the actual schedule

NOT interpolation with respect to increasing vacuum activity orders. When
one single query already connects all its participating marked locations
and output windows this way, just prove its numerical bill. Uses no mixing
hypothesis for these terms; still need mixing for multi-window queries
with e.g. disconnected or short intake support. Even these receipts
stop at a very large arity bound because of the absence of a factorial
allowance beyond the incoming income.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.CalibratedMixedHistory.Bridge
open RG Function Lattice Lattice.Corona Wilson Extra.Trajectories Marker Finset MeasureTheory
  Work.G07 Push.Local.Kernel  Filter Stock Mix Overlay Real
  Push.AbsoluteSums Push.AbsoluteSums.Footprint 
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {C : Family G} {j p N l k : ℕ}

lemma reach (H : Levels G) : Tendsto (fun j => ((H.S.block j).val:ℝ)) atTop atTop := by
  let f := fun j : ℕ => (H.clock.J (j+1):ℝ)
  have he : Tendsto f atTop atTop := tendsto_natCast_atTop_atTop.comp (H.fits.deep.comp (tendsto_add_atTop_nat 1))
  have hx : Tendsto (fun j => f j^2*log 2) atTop atTop :=
    ((tendsto_pow_atTop (n:=2) (by norm_num)).comp he).atTop_mul_const (Real.log_pos (by norm_num))
  apply tendsto_atTop_mono _ (Real.tendsto_exp_atTop.comp hx)
  intro i
  let B := H.params (i+1)
  let Q : ℝ := (H.S.block i).val
  let X := 1 + B.paths + B.width⁻¹ + B.columns + B.clip.relaxation+B.supportExponent
  have hp : 1 < Q := by unfold Q; exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < (3:ℕ)) (H.S.block_large i)
  have hh : log X / log Q ≤ (f i^2)⁻¹ := H.fits.logCost i
  have hs : 2 ≤ X := by unfold X; linarith [B.paths_pos,B.width_pos,B.clip.radius_pos,B.columns_ge,B.price_pos, inv_pos.mpr B.width_pos]
  change exp (f i^2*log 2) ≤ Q
  conv_rhs => rw [← Real.exp_log (zero_lt_one.trans hp)]
  apply exp_monotone
  have h4 : 4 ≤ f i := by unfold f; exact_mod_cast H.clock.adm (i+1)
  have hi : 0 < f i^2 := by positivity
  apply le_trans (mul_le_mul_of_nonneg_left (log_le_log (by norm_num) hs) hi.le)
  exact (mul_le_mul_of_nonneg_left ((div_le_iff₀ (Real.log_pos hp)).mp hh) hi.le).trans_eq (mul_inv_cancel_left₀ hi.ne' _)

def capacity (l : ℕ) (K : ℝ) (H : Levels G) (j : ℕ) := 0 ≤ K ∧ 128*preCost l ≤ H.clock.coverSize j ∧
    2*K*(10*preCost l) ≤ (H.S.block j).val



/-- Conversion conditioned on meeting enough anchors AT THIS GEOMETRY. -/
lemma currency (H : Levels G) {n : ℕ} {A : ℝ} (p : ℕ) (h : capacity l A H j) {b : ℝ}
    (hb : 0 ≤ b) (hi : H.clock.coverSize j*n ≤ 64*k) (hv : (k:ℝ) ≤ (n:ℝ)*preCost l + Footprint.conversion (H.S.oneStep j p) l * b) :
    A * k ≤ b := by
  obtain ⟨hA,hd,hT⟩ := h
  have he : (H.clock.coverSize j:ℝ)*n ≤ 64*(k:ℝ) := by exact_mod_cast hi
  let K := conversion (H.S.oneStep j p) l
  have hz : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hp : n*(preCost l) ≤ k/2 := by linarith only [mul_le_mul_of_nonneg_right hd hz,he]
  have ht : 2*A*K ≤ 1 := by
    unfold K conversion; rw [← mul_div_assoc, div_le_one]; exact hT
    exact_mod_cast (H.S.block j).property
  change (k:ℝ) ≤ n*(preCost l)+K*b at hv
  have hh : (k:ℝ) ≤ 2*(K*b) := by linarith
  nlinarith only [mul_le_mul_of_nonneg_left hh hA,mul_le_mul_of_nonneg_right ht hb]

/-- Pre-block-price to buy interpolation value reserve later; even works
for the reinforced `steps` support exponent. -/
def savings (H : Levels G) := 300+2*(3+log Purse.windowTax+Crude.docket H+301+1)




variable {V : Type} [DecidableEq V] [Fintype V] (R : Marker.Census V)
    (A : Insertions C.path V N p)
    (Y : Net (C.path.levels.clock.coverSize (j+1)) (C.side (j+1) p))
    (c : V → Support (C.side (j+1) p)) (o : V → Site (C.side (j+1) p))
    (Z : Net (C.path.levels.clock.coverSize j) (C.side j p))
    (core : V → Support (C.side j p)) (o' : V → Site (C.side j p))

section
open Alphabet  
variable (s : Multi.Hot R) (q : Multi.Hot (Multi.parts R)) (E : Z.windows.Piece)
    (z : Multi.Hot R → Y.windows.Piece)

/-- One test (note *not* a claim of no response outside such envelopes). -/
def Sawn (l : ℕ) :=
    let B := C.path.levels.clock.coverSize j
    let P t := Footprint.enlargement (C.S.oneStep j p) l B (wall Y R c (t,z t))
    Ac.Spark P q.val.val ∧ wall Z R core (s,E) ⊆ q.val.val.biUnion P ∧
    (q.val.val.card:ℝ) ≤ Real.exp (B:ℝ)

omit [Fintype V] in
/-- Spark/enlargements buy support AFTER contraction even at the full order
parameters. -/
theorem heavy (ht : Tabs C.path.levels) (h : capacity l (savings C.path.levels) C.path.levels j)
    (hh : Sawn R Y c Z core s q E z l) (hk : C.path.levels.clock.coverSize j * q.val.val.card ≤
      64*coverNumber (C.path.levels.clock.coverSize j) (wall Z R core (s,E))) :
    let H := C.path.levels
    let B := H.clock.coverSize j
    let M := H.clock.coverSize (j+1)
    savings H*coverNumber B (wall Z R core (s,E)) ≤ ∑ i∈ q.val.val,(coverNumber M (wall Y R c (i,z i)):ℝ) := by
  intro H B M
  obtain ⟨hx,hq,-⟩ := hh
  have hK : 0 < B := (C.path.levels.budget j).B_pos
  have hL : M ≤ 2*B := by have hv : M^2 ≤ 2*B^2 := ht.grows j; nlinarith
  let a := q.val.val
  let D := wall Z R core (s,E)
  let X t := wall Y R c (t,z t)
  let P t := enlargement (C.S.oneStep j p) l B (X t)
  have hv : coverNumber B D ≤ ∑ t∈a,coverNumber B (P t) := (cover_mono hq B).trans (Ac.cover _ _ hx)
  apply currency H p h (by positivity) hk
  calc
    _ ≤ ∑ t∈a,(coverNumber B (P t):ℝ) := by exact_mod_cast hv
    _ ≤ ∑ t∈a, (preCost l + conversion (C.S.oneStep j p) l*coverNumber M (X t)) := sum_le_sum fun t _ => footprint _ _ _ _ _ hK hL
    _ = _ := by rw [sum_add_distrib,← mul_sum]; simp [a,H,X]


end
end YM.Planned.CalibratedMixedHistory.Bridge
