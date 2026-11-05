import YM.Progress.DIRECTED_RECIPE.Batch
import YM.Progress.DIRECTED_RECIPE.Samples
import YM.Work.H04

/-!
# From this continuity test of pre-transfer data to Curve after assembly

For use with effective estimates on the output regular/compulsory/soft
families before gathering. `Flow` needs convergence with FULL sup norms in
parameter neighborhoods (but per address at fixed period). `PreBound` is a
common summable majorant at that fixed period. No inference from per-address
alone or from essential bounds. Generalizes
the continuity gluing for fixed lists H04 (which suffices for RCake), consumes
Work.H04 proofs for products with common domination. Address and label
transport throughout `T`; uses full order. Does NOT assert the analytics
required on the pre-data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe

open Function Set RG Wilson Lattice RG.Shoot Ovens Ovens.Pipes Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

variable {G : Gauge} {n : Side} {P : BudgetPoint}

namespace Samples

/-- Only at THIS volume; the budgets for `Move` cost real egress mass,
and are not obtained by such a weakening. -/
lemma mass_at_volume {X : ℕ → Support n} {f : ℕ → ℝ}
    (P : BudgetPoint) (hf : ∀ i, 0 ≤ f i) (h : Summable f) : Summable fun i => P.mass (X i) (f i) := by
  let D := (Finset.univ : Finset (Support n)).sup (coverNumber P.B)
  let v := Real.exp (P.supportExponent * D)
  have he i : 0 ≤ P.mass (X i) (f i) := (hf i).trans (P.loMass (X i) (f i) (hf i))
  refine Summable.of_nonneg_of_le he (fun i => ?_) (h.mul_left v)
  have hu : coverNumber P.B (X i) ≤ D := Finset.le_sup (f:=coverNumber P.B) (Finset.mem_univ _)
  exact mul_le_mul_of_nonneg_right (Real.exp_monotone
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hu) P.exponent_pos.le)) (hf i)

/-- abstract passage across address sup tests. -/
lemma accountant {T : Set ℝ} {x : ℝ} {payee : ℕ → Type*} {F : ℝ → (i : ℕ) → payee i → ℝ}
    {A : ℕ → Support n} (P : BudgetPoint) {C : ℕ → ℝ} (hC : ∀ i, 0 ≤ C i) (hc : Summable C)
    (hh : ∀ y∈T, ∀ i k, 0 ≤ F y i k ∧ F y i k ≤ C i)
    (h : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝[T] x, ∀ j, F y i j ≤ ε)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ y in 𝓝[T] x, ∃ f : ℕ → ℝ,
      (∀ i, 0 ≤ f i ∧ ∀ j, F y i j ≤ f i) ∧ SumBudget (fun i => P.mass (A i) (f i)) ε := by
  let D y i := insert 0 (range (F y i))
  let g y i := sSup (D y i)
  have hb {y} (hy : y ∈ T) (i) : 0 ≤ g y i ∧ (∀ j, F y i j ≤ g y i) ∧ g y i ≤ C i := by
    have he : ∀ a∈D y i, a ≤ C i := by
      rintro a (rfl|⟨j,rfl⟩)
      · exact hC i
      exact (hh _ hy i j).2
    have hw : BddAbove (D y i) := ⟨_,he⟩
    exact ⟨le_csSup hw (mem_insert ..),fun j => le_csSup hw (mem_insert_of_mem _ (mem_range_self j)),
      csSup_le ⟨_,mem_insert ..⟩ he⟩
  let bill y i := P.mass (A i) (g y i)
  let cap i := P.mass (A i) (C i)
  have hp i : Tendsto (fun y => bill y i) (𝓝[T] x) (𝓝 0) := by
    have he : Tendsto (fun y => g y i) (𝓝[T] x) (𝓝 0) := by
      refine tendsto_order.mpr ⟨fun r hr => ?_,fun r hr => ?_⟩
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact hr.trans_le (hb hy i).1
      filter_upwards [self_mem_nhdsWithin, h i (r/2) (by linarith)] with y hy hf
      refine lt_of_le_of_lt (csSup_le ⟨_,mem_insert 0 (range (F y i))⟩ ?_) (half_lt_self hr)
      rintro u (rfl|⟨k,rfl⟩)
      · linarith
      exact hf k
    simpa [bill,BudgetPoint.mass] using (he.const_mul (Real.exp (P.supportExponent * (coverNumber P.B (A i) : ℝ))))
  have hs : Summable cap := mass_at_volume P hC hc
  have H y (hy : y∈T) i : 0 ≤ bill y i ∧ bill y i ≤ cap i :=
    ⟨le_trans (hb hy i).1 (P.loMass _ _ (hb hy i).1),
      mul_le_mul_of_nonneg_left (hb hy i).2.2 (Real.exp_pos _).le⟩
  have he : Tendsto (fun y => ∑' i, bill y i) (𝓝[T] x) (𝓝 0) := by
    simpa using tendsto_tsum_of_dominated_convergence hs hp
      (show ∀ᶠ y in 𝓝[T] x, ∀ i, ‖bill y i‖ ≤ cap i by
        filter_upwards [self_mem_nhdsWithin] with y hy i
        exact (Real.norm_of_nonneg (H y hy i).1).trans_le (H y hy i).2)
  filter_upwards [self_mem_nhdsWithin,(tendsto_order.mp he).2 ε hε] with y hy hv
  exact ⟨g y,fun i => ⟨(hb hy i).1,(hb hy i).2.1⟩,
    fun i => (H y hy i).1,hs.of_nonneg_of_le (fun i => (H y hy i).1) (fun i => (H y hy i).2),hv.le⟩

-- unforced derivatives live on the original healthy/support domain including all orders required
private abbrev Read (G : Gauge) (P : BudgetPoint) (A : RegularAddress n) :=
    { p : Config G n × List (Directions G n) // Healthy P.threshold A.support p.1 ∧
      p.2.length ≤ P.order ∧ ∀ i∈p.2, P.dirBound A.site i }

lemma e_samples {T : Set ℝ} {x : ℝ} (hx : x∈T) {E : ℝ → ℕ → Config G n → ℝ} {A : ℕ → RegularAddress n}
    (hE : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝[T] x, variesRegular P (A i) (E x i) (E y i) ε)
    {C : ℕ → ℝ} (hC : Summable C) (hg : ∀ y∈T, ∀ i, P.supBounds (A i).site (A i).support (E y i) (C i))
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ y in 𝓝[T] x, ∃ g : ℕ → ℝ,
      (∀ i, variesRegular P (A i) (E x i) (E y i) (g i)) ∧ SumBudget (fun i => P.mass (A i).support (g i)) ε := by
  let X (y) (i : ℕ) (p : Read G P (A i)) := leftDerivs (E y i) p.val.2 p.val.1
  let D y i p := ‖X x i p-X y i p‖
  have hh y (hy : y∈T) i p : ‖X y i p‖ ≤ C i :=
    (hg y hy i).2 _ p.property.1 _ p.property.2.1 p.property.2.2
  have he := accountant (A:=fun i => (A i).support) P (F:=D) (C:=fun i => C i + C i)
    (fun i => add_nonneg (hg x hx i).1 (hg x hx i).1) (hC.add hC) (fun y hy i p =>
      ⟨norm_nonneg _,(norm_sub_le ..).trans (add_le_add (hh x hx i p) (hh y hy i p))⟩) (fun i r hr =>
      (hE i r hr).mono fun y hy p => hy.2 p.val.1 p.property.1 p.val.2 p.property.2.1 p.property.2.2) ε hε
  filter_upwards [he] with y hy
  obtain ⟨g,hg,H⟩ := hy
  exact ⟨g,fun i => ⟨(hg i).1, fun U hU l hL hl => (hg i).2 ⟨(U,l),hU,hL,hl⟩⟩,H⟩
end Samples

open Samples

/-- Pre-transfer continuity tests, at a fixed geometry and a single Pipes
population used throughout T. No continuity in field across hard tests. -/
structure Flow (P : BudgetPoint) (d : ℝ → Tap G n) (X : Pipes G n) (T : Set ℝ) : Prop where
  regular : ∀ x∈T, ∀ i ε, 0<ε → ∀ᶠ y in 𝓝[T] x, variesRegular P (X.reg i) ((d x).regular i) ((d y).regular i) ε
  reaches : invariantJet P d T

/-- At a fixed volume. Used on sampling sets (when using these
termwise/dominating-family arguments; no necessity for arbitrary full estimates
claimed). -/
structure PreBound (P : BudgetPoint) (d : ℝ → Tap G n) (X : Pipes G n) (T : Set ℝ) : Prop where
  E : ∃ c : ℕ → ℝ, Summable c ∧ ∀ x∈T, ∀ i, P.supBounds (X.reg i).site (X.reg i).support ((d x).regular i) (c i)
  K : ∃ c : Label → ℝ, Summable c ∧ ∀ x∈T, ∀ i U, ‖reach (d x) i U‖ ≤ c i

variable {d : ℝ → Tap G n} {X : Pipes G n} {T T' : Set ℝ}
lemma Flow.tighter (h : Flow P d X T) (hh : T' ⊆ T) : Flow P d X T' :=
  ⟨fun _ hx i ε he => (h.regular _ (hh hx) i ε he).filter_mono (nhdsWithin_mono _ hh),
    fun _ hx i ε he => (h.reaches _ (hh hx) i ε he).filter_mono (nhdsWithin_mono _ hh)⟩

lemma Flow.measured (H : Flow P d X T) (he : PreBound P d X T)
    (F : ℕ ≃ X.Pellet) {x} (hx : x∈T) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ y in 𝓝[T] x, deviation P (fused F P (d x)) (fused F P (d y)) ε := by
  obtain ⟨C,hC,H1⟩ := he.K
  obtain ⟨A,hA,H2⟩ := he.E
  have hg (i) : 0 ≤ C i := (norm_nonneg _).trans (H1 x hx i 1)
  let B := fun i => ∏ k∈(F i).val, C k
  have hb i : 0 ≤ B i := Finset.prod_nonneg fun _ _ => hg _
  have hs : Summable B := (summable_finsetProd_of_summable_nonneg hg hC).comp_injective
    (i:=fun i : ℕ => (F i).val) (Subtype.val_injective.comp F.injective)
  have H' y (hy : y∈T) i U : ‖solid F P (d x) i U-solid F P (d y) i U‖ ≤ B i + B i :=
    (norm_sub_le ..).trans (add_le_add (Work.H04.solid_bound hg H1 _ hx i U) (Work.H04.solid_bound hg H1 _ hy i U))
  have h := accountant (A:=fun i => (addr F P i).support) P (F:=fun y i U => ‖solid F P (d x) i U - solid F P (d y) i U‖)
    (C:=fun i=> B i + B i) (fun i => add_nonneg (hb i) (hb i)) (hs.add hs) (fun y hy i p =>
      ⟨norm_nonneg _,H' y hy i p⟩) (Work.H04.solid_varies hg H1 H.reaches F hx) ε hε
  filter_upwards [h,e_samples hx (H.regular _ hx) hA H2 ε hε] with y hy hw
  obtain ⟨f,hf,hs⟩ := hy; obtain ⟨g,hg,hg'⟩ := hw
  exact ⟨g,f,hg,hf,hg',hs⟩


/-- Optional gate on the test: shared domination need only be requested on the input BEFORE
requiring the operator to realize `PreBound`. One-step checks at an arbitrary
budget point M,f (fine) vs P,n (coarse). This is useful e.g. with reserve
slack in the majorants. `switched` will discharge that shared domination
from the actual input Curve when the implication is used. -/
def Passage {f : Side} (M : BudgetPoint) (Q : ℝ → Rep G f) (δ w : ℝ)
    (P : BudgetPoint) (d : ℝ → Tap G n) (X : Pipes G n) (T : Set ℝ) :=
    ∀ x∈T, ∃ z : ℝ, 0 < z ∧ ∀ s : ℕ → ℝ, (∀ j, s j∈T) → Tendsto s atTop (𝓝 x) →
    Shared M (fun y => (Q y).activities) x (sample x s) (δ+z) (w+z) →
      ∃ r : ℕ → ℕ, StrictMono r ∧ PreBound P d X (sample x (s ∘ r))

lemma switched {f : Side} {M : BudgetPoint} {Q : ℝ → Rep G f} {T : Set ℝ} (h : Curve M Q T) {δ w}
    (hg : ∀ x∈T, (Q x).activities.Valid M δ w) {d : ℝ → Tap G n} (g : Flow P d X T)
    (hf : Passage M Q δ w P d X T) {W : PathData G} {c : Clip} {β v : ℝ → ℝ}
    (hβ : ContinuousOn β T) (hv : ContinuousOn v T)
    (hp : ∀ y∈T, ∃ δ γ, Digests X (d y) P δ γ) :
    Curve P (fun x => finish W c P X (d x) (β x) (v x)) T := by
  refine ⟨hβ,hv,fun _ _ _ _ => rfl,fun _ _ _ _ => rfl,?_⟩
  intro ε he x hx
  let A (y : ℝ) := fused (folio G n) P (Rack.widen X (d y))
  change ∀ᶠ y in 𝓝[T] x,deviation P (A x) (A y) ε
  by_contra hn
  obtain ⟨s, hs, hh⟩ := exists_seq_forall_of_frequently ((not_eventually.mp hn).and_eventually
    (show ∀ᶠ y in 𝓝[T] x,y ∈ T from self_mem_nhdsWithin))
  have hi (i) : s i∈T := (hh i).2
  obtain ⟨z,hz,H⟩ := hf x hx
  have he' := hs.mono_right nhdsWithin_le_nhds
  obtain ⟨r,hr,hp'⟩ := along hx s hi he' h (hg x hx) hz
  have ht := he'.comp hr.tendsto_atTop
  obtain ⟨q,hq,hH⟩ := H (s ∘ r) (fun i => hi (r i)) ht hp'
  let t := (s ∘ r) ∘ q
  let B := sample x t
  have hb : B ⊆ T := sample_sub hx fun i => hi _
  let J := X.encoding.some
  have hc := (within (sample_map x t) (ht.comp hq.tendsto_atTop)).eventually
    ((g.tighter hb).measured hH J (mem_insert ..) ε he)
  obtain ⟨i,hi⟩ := hc.exists
  obtain ⟨_,_,hx'⟩ := hp x hx
  obtain ⟨_,_,hI⟩ := hp (t i) (hb (sample_map x t i))
  exact (hh _).1 ((lift_fused hx' J).compares (lift_fused hI J) hi)
end YM.Progress.DirectedRecipe
