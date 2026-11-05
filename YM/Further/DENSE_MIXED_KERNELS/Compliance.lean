import YM.Further.DENSE_MIXED_KERNELS.Brand
import YM.Further.DENSE_MIXED_KERNELS.Company

/-!
# Dense marker-column identities & cost registration tools

This per-row input is the literal density coefficient *selection*.
Scalar choices, anchors and every moment/mode incidence
still checked by caller. We're not manufacturing convergence of Lambda
series or this row on gratuitous noncommitted masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Function Filter MeasureTheory Measure Finset Lattice RG Wilson Pressure Precision Module Tree
open Push.SectorMeasure Next.Fluctuations.Sector Push.AbsoluteSums Corona Overlay Extra.Multi Labels Marker
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical NNReal ENNReal

namespace Throng
section gauge
-- directly from actual representation on its own; adapted to exponent from SectorMeasure.Presented's eval proof
variable {G : Gauge} {n : Side} {σ C Λ δ w : ℝ} {P : Rep G n}
open YM.Work.F05
lemma veil {E : Type*} [Zero E] {D : Support n} (x : ℝ) {g : Config G n → E} (h : GaugeInvariant g) :
    GaugeInvariant (masked x D g) := by
  intro k U; unfold masked; simp only [Set.indicator,Set.mem_setOf_eq,Healthy,gauge_flags,h k U]; congr!

lemma phase (h : P.Lawful σ C Λ δ w) : GaugeInvariant P.exponent := by
  have hp (s : Site n → G.El) (U : Config G n) (i : Pressure.Cell n) : P.path.baseTerm P.clip P.p (gauge s U) i =
      P.path.baseTerm P.clip P.p U i := by
    simp only [PathData.baseTerm, PathData.kept, face_gauge,G.chord_conj,ell_gauge h.paths,G.norm_adjoint]; congr!
  have hm {k} (h : ℕ→Atom G k) (s : ∀ i, (h i).Invariant) (x : Site n) (t) (U : Config G n) :
      PathData.atomSeries h P.p (gauge t U) x = PathData.atomSeries h P.p U x := by
    apply tsum_congr; intro i; refine veil (D:=(h i).footprint x) (g:=fun y => (h i).unmasked y x) _ ?_ t U
    intro t U; unfold Atom.unmasked; simp_rw [slot_gauge]; exact s i ..
  intro t U
  have he (i : ℕ) : P.activities.regularOccurrence P.p i (gauge t U) = P.activities.regularOccurrence P.p i U :=
      veil _ (h.labels.regular.smooth i).symmetry ..
  simp only [Rep.exponent,PathData.inChannels,PathData.principal, pull_gauge_zero,hp, hm P.path.cubic (fun i => (h.paths.invariant i).2.1), hm P.path.quartic (fun i => (h.paths.invariant i).2.2), hm P.path.loop (fun i => (h.paths.invariant i).1),Activities.additive,he]


end gauge

variable {c f : Side} {G : Gauge} {A : ChartRatio G} (H : Port A)
    {S : StepData c f} {x W γ σ σ' C C' Λ Λ' δ δ' w w' : ℝ}
    {R : Rep G f} {P : Rep G c} {T : Tube G S} {V α β I : Type} [DecidableEq V] {L : Census V}
    {X : Chain (α⊕β)} {ρ : α→Pieces} {o : X.Index}

lemma mentions {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (F : Forest S.ratio)
    (K : Allocation G S x W) (β : ℝ) (f : Config G _→X) (Y : Stores S) (V : Config G c)
    (h : RG.flags (temp x) V ≠ Y.flags) : output K F β f Y V=0 := by
  refine Finset.sum_eq_zero fun k _ => integral_eq_zero_of_ae (Eventually.of_forall fun v => ?_)
  unfold Allocation.portion
  have ht : K.bill Y k (F.drape v) V=0 := by by_contra hh; exact h (K.actual _ _ _ _ hh).exactFlags.symm
  rw [ht,zero_smul]; rfl

variable (K : Allocation G S x W) (Y : Stores S) (a : Associates X ρ)
    (D : Bands L R)
    (h : Throng Y x) (hr : R.Lawful σ C Λ δ w) (hp : P.Lawful σ' C' Λ' δ' w')
    (hb : 0≤R.beta) (ht : Throng.Fits T P R x) (Hq : S.patch.Branches S.kernel G)
    (hh : PointCharge T x W γ) (hw : 0≤w) {l m : ℝ} (hl : l ≤ m) (he : 0 ≤ m)

variable {B : ℝ} {e : Pieces→ℝ} (hD : D.Active) (hz : Inbox D B e) (hB : B ≤ 1)
include hr Hq hD hz hB


include hD h hp hb ht hh hw hl he

-- support full; provider can check F.hard.value on all V via this pointwise identity. Doesn't assert
-- coherence after log. Extensivity gain **only here** where obligatory support full, even in REAL
-- layer overlap. Anti-registration duplication still checked (can't count one ticket more than once).
theorem charges (g : ℝ) (F : Forest S.ratio) (U : Config G c) :
    output K F R.beta (ticket D X ρ a.Ks) Y U = base S P R l U •
      (if Finset.univ ∩ RG.flags P.p.threshold U = Y.flags then (brand D ρ F H K Y P l a.Ks a.wherePack).value g U else 0) := by
  have hx := (travels D ρ F H K Y P a.Ks a.wherePack h hr hp hb ht Hq hh hw he hl g U hD hz hB).2
  simp only [a.denominator,one_smul] at hx; split
  · exact hx.symm
  next v => rw [mentions .., smul_zero]; rw [univ_inter,ht.awake] at v; exact v

-- Also compatible average under supplied natural Allocation K (both existing generators)
variable [Fintype I] (Wv : Vault I S)

end Throng
end YM.Further.DenseMixedKernels
