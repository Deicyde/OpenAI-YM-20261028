import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Annulus
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Census


/-!
# Cost of the full H200 remainder, on the same underlying strike

Even disconnected A at this point. Multiplicities & charges per all
channels, full Y. The post-L constant μ at issuance buys this on the
same orientation service. Nothing about V gradients yet. `Roots` still
need the missing costs incl. stationary/local-Gaussian and norm ratios.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

namespace Coat
variable (X : Coat T F)
lemma expenses (Z : Stores S) (s : Signed) (u : Directions G f) (hq : Z.place ⊆ X.seeds.place) {E : ℝ}
    (he : 0 ≤ E) (h : ∀ p : Spot c f, Inside (X.addr s p) Z (200*X.B) → ¬ Inside (X.addr s p) Z (2*X.B) →
      -E ≤ X.debit u s p) :
    (turnStore s Z).assessed T X.x (pull s 0 (X.input u))
        (S.prediction (pull s 0 (X.input u)) (choice s X.k)) (pull s 0 X.V)-
          E*(Animals.ballCost (200*X.B+1):ℝ)*(Census.spots S.patch.L:ℝ)*Z.shares ≤
          X.assigned Z u s := by
  let C := turnStore s Z
  let B := X.B
  let A := posted C (200*X.B)
  let D := posted C (2*X.B)
  have hp : D ⊆ A := fun p hh => mem_filter.mpr ⟨mem_univ _,
    Lattice.Corona.halo_mono (show 2*B ≤ 200*B by omega) (Finset.Subset.refl _) (mem_filter.mp hh).2⟩
  have he' p (hh : p ∈ A \ D) : -E ≤ X.debit u s p := h p ((Census.posted_here ..).1 (mem_sdiff.mp hh).1)
    ((Census.posted_here ..).not.mp (mem_sdiff.mp hh).2)
  rw [← X.core Z hq]
  change (∑ p ∈ D,_) - _ ≤ ∑ p∈ A, X.debit u s p
  rw [← Finset.sum_sdiff hp]
  apply sub_le_iff_le_add.mpr
  rw [add_right_comm (∑ x∈A \ D, _)]
  apply le_add_of_nonneg_left
  have hv : (↑(A \ D).card:ℝ) ≤ ↑Z.shares* ↑(Animals.ballCost (200*X.B+1)) * ↑(Census.spots S.patch.L) := by
    rw [← same_price s Z]; exact_mod_cast (card_le_card sdiff_subset).trans (Census.postedBound C (200*X.B))
  have hh := sum_le_sum (f:=fun _ => -E) (s:=A \ D) he'
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  nlinarith only [hh,mul_le_mul_of_nonneg_left hv he]

/-- Need `S.patch=D` (proof-time shape only), chart quote hAccess
post L, W as asked. If using with hγ reserve choose it before this bill.
`E` used AGAIN when paying analytic exponents, contracts expose it here. -/
theorem earns (P : Teller G) (L : Side) (D : Patch) (hd : D.Branches P.bind G) (A : ℝ) (hA : 0<A)
    {w : ℝ → ℝ} (h : Rate G L (-(1/2)) w) (hp : ∀ᶠ x in atTop, 0 ≤ w x) :
    ∃ E : ℝ → ℝ, Rate G L (-(3/2)) E ∧ ∀ᶠ x in atTop,
    0 ≤ E x ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio)
      (X : Coat T F), X.x=x → S.patch=D → S.patch.L=L → Room P S T x →
      ∀ (Z : Stores S) (u : Directions G f) (W γ κ : ℝ), Z.place ⊆ X.seeds.place →
      (∀ V, Bid.Maximum A T x V) → PointCharge T x W κ → ShellAccess S G X.x W X.width γ →
      γ*(2*(X.width*X.t)) ≤ w x → Controlled X (304*X.B) Z u (w x) →
      Tags.Wide Z (300*X.B) (X.input u) X.k X.V X.x W →
        (κ * X.t^2 - E x)*Z.shares ≤ X.quoteNear Z u := by
  obtain ⟨Y,y,H⟩ := annulus P L D hd A hA h hp
  let E x := Y x*(Animals.ballCost (200*radiusB x+1):ℝ)*(Census.spots L:ℝ)
  have hf : Rate G L (-(3/2)) E := by
    simpa only [add_zero] using! ((y.mul (Census.width_rate G L 200 1)).mul_right (Census.spots L))
  refine ⟨E,hf,H.mono ?_⟩
  intro x hx
  refine ⟨by unfold E; have h := hx.1; positivity,?_⟩
  intro c f S T F X hx' hS hL hr Z u W γ κ hz hm hq he hf hh ht
  subst x
  let v := Z.shares
  let t := X.t
  let U := X.input u
  let M := meanEnergy Z T X.x U X.k X.V
  have Hm : κ*t^2*v ≤ M := ht.bought (by unfold Coat.B; omega) (SectorMeasure.funds_branch hr.accepted) F (X.sliced u) hq
  have hy (s : Signed) := expenses X Z s u hz hx.1 fun p hi hj =>
    hx.2 c f S T F X rfl hS hL hr Z u p s W γ (hm _) he hf hh ht hi hj
  rw [sub_mul]
  apply le_trans (sub_le_sub_right Hm _)
  unfold M meanEnergy quoteNear
  rw [← av_const (E _ * _),← av_sub];
  apply av_mono
  intro s
  have he := hy s; rw [hL] at he; exact he
end Coat
end YM.ConnectedActivityE6
