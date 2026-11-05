import YM.RG08.Rate.Ascent

/-!
# Strict event price receipts for formal flow

Feed `flow_bounds` the one-step majorants in the following *local* form (∀ X in one schedule/demand
problem):

* Only same-grade inheritance uses current grade from previous scale. Pay it immediately by a
  prelength contraction, including ALL alignment, path choice and reset operations on the
  self-edge. Account `θ` is for fixed finite demands but independent of `X`, hence independent of
  L and stage when ranging over those data. Convey this on both sides.
* Forcing may be polynomial in earlier-grade bills at coarse and fine side taken together, with
  polynomial-age caps C absorbing all finite uses; common exponent d (or make d a grade index).
* For cutoff differences, charge strict predecessor differences and the one-step cutoff defect
  `flat` (including all flat ingredients, typically coarser-top power measured at fine side),
  possibly multiplied even by the entire forcing polynomial. Both histories' absolute bills must
  be included in `f` *also for the current grade* (`amount`); in a T^N-T^∞ insertion in the
  repeated-rank component the fine datum is at **that same grade**. No same grade *differences*
  can be included here: pay those only in `drop`. Top differences may grow with age (polynomial).

This is a convenient sufficient shape, not necessary (manual uses of `fade_rec`/`poly_rec` can
admit any finite acyclic grade sets and forcing powers). Neither labels nor coupling domains nor
which histories have these inputs are specified here. This file provides the quantitative algebra
only.
-/
noncomputable section
namespace YM.RG08.Rate.Stair
open Finset
set_option autoImplicit false
universe v w
variable {X : Type v} {V : Type w} {W : Stair X}

/-- Finite strict events. Can pick V itself infinite if each result only takes finitely many
predecessors and rank is well-founded. -/
structure Charges (V : Type w) where
  prior : V → Finset V
  rank : V → ℕ
  strict j k : k ∈ prior j → rank k < rank j

namespace Charges
variable (P : Charges V)

def earlier (j : V) (f : V → Array X) (W : Stair X) : Array X :=
    fun x i => ∑ k ∈ P.prior j,(f k x i+W.nextUp (f k) x i)

/-- Includes current grade in the absolute polynomial on the difference side. -/
def amount (j : V) (f : V → Array X) (W : Stair X) : Array X :=
    fun x i=> f j x i+W.nextUp (f j) x i+P.earlier j f W x i

theorem poly_prior (j : V) {f : V → Array X} (h : W.Admits)
    (hr : ∀ k ∈ P.prior j, W.Poly (f k)) : W.Poly (P.earlier j f W) :=
  Poly.sum _ (fun k x i=> f k x i+W.nextUp (f k) x i) fun k hk=> (hr k hk).add ((hr k hk).finer h)

theorem fade_prior (j : V) {f : V → Array X} (h : W.Admits)
    (hr : ∀ k ∈ P.prior j, W.Fade (f k)) : W.Fade (P.earlier j f W) :=
  Fade.sum _ (fun k x i=>f k x i+W.nextUp (f k) x i) fun k hk=> (hr k hk).add ((hr k hk).finer h)

end Charges
variable {f u : V → Array X} {P : Charges V} {θ : V → ℝ}

/-- Separate the two bullets so solved bounds on either history can be fed at different `top`s. -/
structure Provisions (P : Charges V) (W : Stair X) (f : V → Array X) (θ : V → ℝ) where
  cap : V → Array X
  d : V → ℕ
  gain j : 0 < θ j
  costing j : W.Poly (cap j)
  here j x i : W.Here x i → 0 ≤ f j x i
  boundary j x (h : W.Here x (W.top x)) : f j x (W.top x) ≤ cap j x (W.top x)
  step j x i (h : W.Here x i) (hi : i < W.top x) : f j x i ≤ f j x (i+1)*W.drop (θ j) x i +
      cap j x i*(1+P.earlier j f W x i)^d j

theorem poly_events (ha : W.Admits) (h : Provisions P W f θ) : ∀ j, W.Poly (f j) := by
  refine poly_rec (measure P.rank).wf θ h.gain f h.here fun j hj => ?_
  have hr := P.poly_prior j ha fun k hk=> hj k (P.strict j k hk)
  let g (j) (x:X) (i:ℕ) := h.cap j x i*(1+P.earlier j f W x i)^h.d j
  have hs : W.Poly (g j) := (h.costing j).mul (((Poly.constant W zero_le_one).add hr).pow (h.d j))
  refine ⟨g j,hs,fun x i hi=> ?_⟩
  unfold stepOnly; split
  · exact h.step j x i hi ‹_›
  rename_i hr'
  have he : i = W.top x := le_antisymm hi.2 (Nat.le_of_not_gt hr'); subst i; rw [zero_add]
  apply (h.boundary j x hi).trans
  unfold g
  exact le_mul_of_one_le_right ((h.costing j).nonneg hi) (one_le_pow₀ (by linarith [hr.nonneg hi]))

structure Deviations (P : Charges V) (W : Stair X) (f u : V → Array X) (θ : V → ℝ) where
  cap : V → Array X
  d : V → ℕ
  flat : V → Array X
  pricing j : W.Poly (cap j)
  delay j : W.Fade (flat j)
  entry j x (h : W.Here x (W.top x)) : u j x (W.top x) ≤ cap j x (W.top x)
  here j x i : W.Here x i → 0 ≤ u j x i
  step j x i (h : W.Here x i) (hi : i < W.top x) : u j x i ≤ u j x (i+1)*W.drop (θ j) x i +
      cap j x i*(1+P.amount j f W x i)^d j*(flat j x i+P.earlier j u W x i)

theorem cutoff_events (ha : W.Admits) (hu : ∀ j, 0 < θ j)
    (hf : ∀ j, W.Poly (f j)) (h : Deviations P W f u θ) : ∀ j, W.Fade (u j) := by
  refine fade_rec (measure P.rank).wf θ hu u h.here fun j hj=>?_
  have hr := P.fade_prior j ha fun k hk=>hj k (P.strict j k hk)
  have hp : W.Poly (P.amount j f W) := ((hf j).add ((hf j).finer ha)).add (P.poly_prior j ha fun k _=> hf k)
  let g x i := h.cap j x i*(1+P.amount j f W x i)^h.d j*(h.flat j x i+P.earlier j u W x i)
  let b x i := if i=W.top x then h.cap j x i else 0
  have hg : W.Fade g := ((h.pricing j).mul (((Poly.constant W zero_le_one).add hp).pow _)).fade ((h.delay j).add hr)
  have hb : W.Fade b := by
    apply Fade.of_top ((h.pricing j).mono ?_)
    · intro x i hi hx; exact if_neg (Nat.ne_of_lt hx)
    intro x i hi; have hq:= (h.pricing j).nonneg hi; unfold b; split <;> simp [hq]
  refine ⟨_,hg.add hb,fun x i hi=>?_⟩
  dsimp only [Stair.stepOnly,b]; split
  · rename_i he; rw [if_neg (Nat.ne_of_lt he), add_zero]; exact h.step j x i hi he
  rename_i he; have hv := le_antisymm hi.2 (Nat.le_of_not_gt he); subst i; rw [zero_add,if_pos rfl]; exact (h.entry j x hi).trans (le_add_of_nonneg_left (hg.nonneg hi))

theorem flow_bounds (ha : W.Admits) (hf : Provisions P W f θ) (h : Deviations P W f u θ) (j : V) : W.Poly (f j) ∧
    ∃ (A : ℝ) (d : ℕ) (c : ℝ), 0 ≤ A ∧ 0<c ∧
      ∀ x i, W.Here x i → 0 ≤ u j x i ∧
        u j x i ≤ A * W.age x i^d * (((W.sched x).a (W.top x) / (W.sched x).a i)^c) := by
  have hp := poly_events ha hf
  exact ⟨hp j,(cutoff_events ha hf.gain hp h j).cap⟩

end YM.RG08.Rate.Stair
