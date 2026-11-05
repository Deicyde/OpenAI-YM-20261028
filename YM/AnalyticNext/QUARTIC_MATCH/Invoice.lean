import YM.AnalyticNext.QUARTIC_MATCH.Cells.Entry
import YM.AnalyticNext.QUARTIC_MATCH.Delivery

/-!
# The analytic invoice for multiperiod quartic matching

Once an exponentially localized RESIDUAL on actual link tensors is known
(E- ff style), even initially JUST on the finite real tori,
use this module. This file separates that cost from the issuance of nonlinear
output arrays meeting TRUE path charges. No earnings from scaling on only
one period. No repeating an exponent deduction here for next vacuum step.

Keep the two cost inputs (`writes`). Could for example use just post-L `Spatial`
on auxiliary sizes (not necessarily tracking pre-L prices α). Construct the
periodising array this way. *Then*, before issuing paths, it has the pre-L
rate/cost too provided that estimate is achieved on the probes on the
genuine schedule. See `Range`, `Local`. Doesn't cost a factor of volume per p.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch
open Lattice RG Precision Bid Function Matrix Wilson Exterior Filter Laurent Tensor Joint BoxChain
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
namespace Mail
variable {G : Gauge} {n : ℕ} (P : Printed n)

/-- Residual formulas on all admitted multiplexes. -/
structure Law (L : ℕ) (F : (c : Side) → Dom G n c) : Prop where
  color (c : Side) : L ≤ c.val → Colorwise (F c)
  cover (c : Side) : L ≤ c.val → Uniform (F c)
  test (c d : Side) : L ≤ c.val → L ≤ d.val → (h : c.val∣d.val) → Compatible h (F d) (F c)

namespace Law
variable {L : ℕ} {F : (c : Side)→ Dom G n c}

def raw (h : Law L F) : Bills (Fin n) (ColorPart G n) := fun c =>
    if hc : L ≤ c.val then entries (F c) (h.color c hc) else 0

lemma raw_buys (h : Law L F) {c : Side} (hc : L≤c.val) : h.raw c=entries (F c) (h.color c hc) := dif_pos hc
lemma cash (h : Law L F) (j : Fin n) : Weave j L h.raw := by
  refine ⟨fun {c} hx => by rw [h.raw_buys hx]; exact entries_cohere _ _ (h.cover c hx),?_⟩
  intro c d hc hd hv X; rw [h.raw_buys hc,h.raw_buys hd]
  exact is_periodic hv j _ _ _ _ (h.cover d hd) (h.test c d hc hd hv) X

/-- Compare exact periodized array values. Use when rank unavailable at some extensions. -/
theorem upstream (h : Law L F) (j : Fin n) {X : ArrayC (Fin n) ℤ (ColorPart G n)} {σ C : ℝ}
    (hp : Pricing X σ C) (he : ∀ (c : Side), L ≤ c.val → h.raw c=scene c j X)
    {d : ℕ → Side} (hd : ∀ i, L ≤ (d i).val) (hm : Tendsto (fun m => (d m).val) atTop atTop)
    (hy : ∀ i, Residual.Legal (F (d i))) {A b : ℝ}
    (hq : ∀ i, Spatial (h.raw (d i)) A b) :
    Pricing X A b ∧ ∀ k : Fin n, Rank X k 1 ∧ ClosedSlot X k := by
  have Hv i := h.raw_buys (hd i)
  have ht (V : Fin n → Cell ℤ) : Tendsto (fun i => h.raw (d i) (tor (d i) ∘ V)) atTop (𝓝 (X V)) := by
    simp_rw [he _ (hd _)]
    exact fixed j hp d hm V
  refine ⟨rates (F:=h.raw) hm (Eventually.of_forall hq) ht hp.same,fun k => ⟨fun W hW => ?_,?_⟩⟩
  · have ha i : h.raw (d i) (tor (d i) ∘ W) = 0 := by
      rw [Hv]; exact entries_rank _ _ k _ hW
    have hv := ht W; simp_rw [ha] at hv; exact tendsto_nhds_unique hv tendsto_const_nhds
  funext W
  have ha i : scene (d i) j (lower k X) (tor (d i) ∘ W) = 0 := by
    rw [← descend_lower (d i) j k hp, ← he _ (hd i), Hv, entries_closed _ _ (hy _)]
    rfl
  have hb := fixed j (hp.smaller k) d hm W
  simp_rw [ha] at hb
  exact tendsto_nhds_unique hb tendsto_const_nhds

end Law

section prices
variable (G) (n : ℕ) [NeZero n]

/-- Uniformly before volume, independent of step and P schedule application.
Angular/global invariance for the output used in the final equality. -/
theorem writes (P : Printed n) (hn : 2 ≤ n) (σ : ℝ) (hp : 0 < σ) :
    ∃ δ Q : ℝ, 0<δ ∧ 0 ≤ Q ∧ ∀ L (F : (c : Side)→Dom G (n+1) c) (H : Law L F),
      (∃ R C : ℝ, ∀ (c : Side), L ≤ c.val → Spatial (H.raw c) R C) →
      ∀ (d : ℕ → Side), (∀ i, L ≤ (d i).val) → Tendsto (fun m => (d m).val) atTop atTop →
        (∀ i, Residual.Legal (F (d i))) → ∀ B : ℝ, (∀ i, Spatial (H.raw (d i)) σ B) →
          ∃ A : rootArray G n,
            SumBudget (fun i => (letters P A i).budget δ) (Q*B) ∧
            ∀ i, Tensor.coeff (impact (c:=d i) (letters P A)) (n+1) 0=F (d i) ∧
              ∀ j, j<n+1 → Tensor.coeff (impact (c:=d i) (letters P A)) j 0=0 := by
  haveI := FiniteDimensional.complete ℝ (ColorPart G (n+1))
  obtain ⟨u,v,hu,hh,hv,H⟩ := BoxChain.multi (V:=ColorPart G (n+1)) n hn σ hp
  refine ⟨P.width u,P.reserve G u*v,P.expans hu,mul_nonneg (P.reserve_nonneg G u hu) hv,?_⟩
  intro L F Hf hm d hd hD hw B hb
  obtain ⟨R,C,HX⟩ := hm
  obtain ⟨X,h1,h2⟩ := Weave.enough (i:=(0:Fin (n+1))) (Hf.cash 0) HX
  obtain ⟨hp,hx⟩ := Hf.upstream 0 h1 h2 hd hD hw hb
  obtain ⟨A,hA,hT,hk⟩ := H B X hp hx
  refine ⟨A,by rw [mul_assoc]; exact sends P hA,fun i => retained P A (hw i) ?_ hA hk⟩
  exact (Hf.raw_buys (hd i)).symm.trans ((h2 (d i) (hd i)).trans (congr_arg (scene (d i) 0) hT))
end prices
end Mail
end YM.AnalyticNext.QuarticMatch
