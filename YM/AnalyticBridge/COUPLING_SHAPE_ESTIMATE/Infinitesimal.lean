import YM.Next.MAXWELL.Simple
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
import YM.Work.C01
import YM.Work.F03.Calculus



/-!
Gauge invariance of a local *unmasked* function. Gradients here really are
null directions of its log-coordinate Hessian; the first-jet step matters in
passing through changes of coordinates. No smoothness of a flag selector.
-/

set_option autoImplicit false
noncomputable section

namespace YM.AnalyticBridge.CouplingShape
open Function Filter Lattice Wilson RG Work ProjectorNext.Equivariance
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side} {X : Support n} {p : BudgetPoint} {f : Config G n → ℝ}

lemma clear_one (p : BudgetPoint) (X : Support n) : Healthy (G:=G) p.threshold X 1 := by
  refine Finset.disjoint_left.mpr fun _ _ hu => ?_
  obtain ⟨i,-,hv⟩ := (flags_spec ..).mp hu; simp [faceValue,square,travel] at hv
  exact hv.not_ge p.threshold_pos.le

lemma flat_C2 (h : p.Regular X f) : ContDiffAt ℝ 2 (f ∘ increment 1) 0 := by
  apply (h.smooth 1 (clear_one ..)).of_le
  exact Nat.cast_le.mpr (Nat.le_trans (by decide : 2 ≤ 6) p.order_ge)

def globalAd (u : G.El) (A : Directions G n) : Directions G n := fun e => G.adjoint u (A e)

lemma overall (u : G.El) (A : Directions G n) (t : ℝ) :
    increment 1 (t • globalAd u A) = gauge (fun _ => u) (increment 1 (t • A)) := by
  funext e
  simp only [increment, Pi.smul_apply, Pi.one_apply, mul_one,Lattice.gauge,globalAd,←map_smul]
  rw [exp_adjoint]


lemma no_current (hs : G.Simple) (h : p.Regular X f) : fderiv ℝ (f ∘ increment 1) 0 = 0 := by
  let L := fderiv ℝ (f ∘ increment 1) 0
  have hL (A : Directions G n) : HasDerivAt (fun t : ℝ => f (increment 1 (t • A))) (L A) 0 :=
    Push.side _ ((flat_C2 h).differentiableAt (by simp)) A
  have hu : GaugeInvariant f := h.symmetry
  have hi (A : Directions G n) (u : G.El) : L (globalAd u A)=L A := by
    have hz := hL (globalAd u A); simp_rw [overall,fun t : ℝ => hu (fun _ => u) (increment 1 (t • A))] at hz; exact hz.unique (hL A)
  have single (A : Directions G n) (e : Edge (Site n)) : L (Pi.single e (A e))=0 := by
    let v := L.toLinearMap ∘ₗ LinearMap.single ℝ (fun _ : Edge (Site n) => G.Color) e
    have hv : Maxwell.Free.irreduc (G:=G) v := fun u x => by
      change L (Pi.single e (G.adjoint u x)) = L (Pi.single e x)
      nth_rw 2 [← hi _ u]
      congr 1
      ext1 j; by_cases hj : j=e
      · subst j; simp [globalAd]
      simp [globalAd,hj]
    change v (A e)=_
    rw [Maxwell.Free.singles_inv hs v hv]; rfl
  ext1 A
  change L A=0
  calc
    _ = L (∑ e, Pi.single e (A e)) := by rw [Finset.univ_sum_single]
    _ = 0 := by rw [map_sum]; exact Finset.sum_eq_zero fun e _ => single A e

def H (f : Config G n → ℝ) : Directions G n →L[ℝ] Directions G n →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ (f ∘ increment 1)) 0

lemma log_eq_H (f : Config G n → ℝ) (A B : Directions G n) : logHessian f A B=H f A B := by
  simp only [logHessian,H,iteratedFDeriv_two_apply]; rfl

lemma symmetric (h : p.Regular X f) (A B) : H f A B=H f B A := by
  rw [← log_eq_H,← log_eq_H]; exact F03.hessian_symmetric (flat_C2 h) A B

lemma diagonal (hs : G.Simple) (h : p.Regular X f) (A) : H f A A = iteratedDeriv 2 (fun t : ℝ => f (increment 1 (t • A))) 0 := by
  rw [← log_eq_H]; exact (F03.line_second (flat_C2 h) (no_current hs h) A).symm

/-- Adds in each slot of a symmetric bilinear; use on subfamilies of directions. -/
lemma polar (h : p.Regular X f) (A B) : H f (A+B) (A+B)=H f A A+2*H f A B+H f B B := by
  simp only [map_add, add_apply,symmetric h B A]; ring

/-- Sign convention of `Lattice.gauge`. -/
def slope (φ : Site n → G.Color) : Directions G n := fun e => φ e.1 - φ (e.1+step e.2)

private def follow (A : Directions G n) (φ : Site n → G.Color) (t : ℝ) := gauge (fun x => G.lieExp (t • φ x)) (increment 1 (t • A))
private def logFollow (A : Directions G n) (φ : Site n → G.Color) (t : ℝ) : Directions G n := fun e => G.plog (G.mat (follow A φ t e))

private lemma follow_zero (A : Directions G n) (φ : Site n → G.Color) (e) : follow A φ 0 e=1 := by simp [follow,Lattice.gauge,increment]
private lemma logFollow_zero (A : Directions G n) (φ : Site n → G.Color) : logFollow A φ 0=0 := by funext e; simp [logFollow,follow_zero]

private lemma logFollow_diff (A : Directions G n) (φ : Site n → G.Color) : ContDiffAt ℝ ω (logFollow A φ) 0 := by
  apply contDiffAt_pi.mpr; intro e
  refine (show ContDiffAt ℝ ω G.plog (G.mat (follow A φ 0 e)) by rw [follow_zero,G.mat_one]; exact G.plog_diff).comp 0 ?_
  have he (a : G.Color) : ContDiff ℝ ω (fun t : ℝ => G.mat (G.lieExp (t • a))) := G.exp_jet.comp (contDiff_id.smul contDiff_const)
  simp only [follow,Lattice.gauge,increment,Pi.one_apply,Pi.smul_apply,mul_one,G.mat_mul,G.mat_inv]
  exact (((he _).mul (he _)).mul ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.comp (he _))).contDiffAt

private lemma handle (A : Directions G n) (φ : Site n → G.Color) :
    (increment 1 ∘ logFollow A φ) =ᶠ[𝓝 0] follow A φ := by
  have hh (e : Edge (Site n)) : ∀ᶠ t in 𝓝 0, G.lieExp (G.plog (G.mat (follow A φ t e)))=follow A φ t e := by
    have hc : Continuous fun t : ℝ => follow A φ t e := by
      simp only [follow,Lattice.gauge,increment,Pi.smul_apply]; fun_prop
    apply (show Tendsto (fun t => follow A φ t e) (𝓝 0) (𝓝 1) from by simpa only [follow_zero] using hc.tendsto 0).eventually G.plog_right
  filter_upwards [eventually_all.mpr hh] with t ht
  exact funext fun e => by simpa only [increment, Function.comp_apply, Pi.one_apply,mul_one,logFollow] using ht e

private lemma expLine (c : G.Color) : HasDerivAt (fun t : ℝ => G.mat (G.lieExp (t • c))) (G.colorMat c) 0 := by
  have ht : HasDerivAt (fun t : ℝ => t • c) c 0 := by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const c
  exact G.expDiff_zero.comp_hasDerivAt_of_eq (0:ℝ) ht (by simp)

private lemma follow_jet (A : Directions G n) (φ : Site n → G.Color) : deriv (logFollow A φ) 0=A+slope φ := by
  funext e
  let d := logFollow A φ
  have hd := ((logFollow_diff A φ).differentiableAt (by simp)).hasDerivAt
  have he : HasDerivAt (fun t : ℝ => G.mat (follow A φ t e)) (G.colorMat (A e+(slope φ) e)) 0 := by
    simp only [follow,Lattice.gauge,increment,Pi.one_apply,Pi.smul_apply,mul_one,G.mat_mul,G.mat_inv]
    convert! ((expLine (φ e.1)).mul (expLine (A e))).mul (expLine (φ (e.1+step e.2))).star using 1
    simp [slope,G.colorMat_skew]; abel
  apply G.colorMat_injective
  have hz : HasDerivAt (fun t : ℝ => G.mat (G.lieExp (d t e))) (G.colorMat (deriv d 0 e)) 0 := by
    refine G.expDiff_zero.comp_hasDerivAt_of_eq (0:ℝ) ((hasDerivAt_pi ..).mp hd e) ?_
    simp [d,logFollow_zero]
  refine (hz.congr_of_eventuallyEq ((handle A φ).mono (p:=fun t => _ = follow A φ t) (fun t ht => ?_))).unique he
  rw [← ht]; simp only [comp_apply,increment,Pi.one_apply,mul_one]; rfl

lemma absorbs (hs : G.Simple) (h : p.Regular X f) (φ : Site n → G.Color) (A) : H f A (slope φ)=0 := by
  have hz (B : Directions G n) : H f (B+slope φ) (B+slope φ)=H f B B := by
    let g := logFollow B φ; let F := f ∘ increment 1
    have he : F ∘ g =ᶠ[𝓝 0] fun t : ℝ => f (increment 1 (t • B)) := (handle B φ).mono fun t ht => by
      change f _=f _; rw [show increment 1 _ = follow B φ t from ht]; exact h.symmetry _ _
    have ha : ContDiffAt ℝ 2 F (g 0) := by unfold g; rw [logFollow_zero]; exact flat_C2 h
    have hd : H f (B+slope φ) (B+slope φ) = iteratedDeriv 2 (F ∘ g) 0 := by
      rw [iteratedDeriv_vcomp_two ha ((logFollow_diff B φ).of_le le_top),show g 0=0 from logFollow_zero ..,
        show deriv g 0=B+slope φ from follow_jet ..,show fderiv ℝ F 0=0 from no_current hs h]
      simp [iteratedFDeriv_two_apply,H,F]
    rw [hd, diagonal hs h B]; exact (he.iteratedDeriv _).self_of_nhds
  have hw := hz 0; simp only [zero_add,map_zero] at hw
  have hq := hz A
  rw [polar h,hw] at hq; linarith

lemma H_local (hs : G.Simple) (h : p.Regular X f) {A B : Directions G n} (C : Directions G n)
    (he : ∀ e : Edge (Site n), e.1∈X → e.1+step e.2∈X → A e=B e) : H f A C=H f B C := by
  have hx {A B : Directions G n} (he : ∀ e : Edge (Site n), e.1∈X → e.1+step e.2∈ X → A e=B e) : H f A A=H f B B := by
    rw [diagonal hs h,diagonal hs h]
    congr 2
    ext1 t; exact h.sites _ _ (fun e ha hb => by simp only [increment, Pi.smul_apply,he e ha hb])
  have hh : H f (A+C) (A+C)=H f (B+C) (B+C) := hx (fun e ha hb => by simp [he e ha hb])
  rw [polar h,polar h,hx he] at hh; linarith

end YM.AnalyticBridge.CouplingShape
