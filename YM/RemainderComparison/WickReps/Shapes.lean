import YM.RemainderComparison.Portal.Crests
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Tir
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Trimmings
import YM.RemainderComparison.Arc.Witness
/-!
# Pose stencils on arbitrary period with aperture reserve B.M
 Support-oriented probes *at any output rooted position* for the
 marks. We also need orientation-compaction and constant off-loading on
 the unmarked law, with estimates at any V including seams.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.WickReps
open Function Filter Lattice RG Pressure Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide Trio
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open YM.RemainderComparison.Aux Portal
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{n c C f L : Side} {Y:Stars→Side} {P:BudgetPoint}{r z k w m p:ℕ}{a b β v R e x:ℝ}

-- while r-variable aperture comp uses Baker
lemma calibrated (g: Config G f→ℝ) (h:Arc.Deduct G P β z R)(hp:2*z < c.val)(A: 2*w≤ f.val)(hq:w+1≤ z) (hf:P.Regular univ g)(ht:0 ≤ b)(hg: Portal.Mare P g β R b)(u:Site c) : let v:=g∘shape (cognac A) u; P.Regular (neighbors z u) v∧ P.supBounds u (neighbors z u) v (Trio.tilt P z * b):=by
   intro v; let s:=neighbors z u; have hh : P.Regular s v:= Arc.regular u hq hf; refine ⟨hh, mul_nonneg (by unfold Trio.tilt; positivity) ht, fun V hu l hl hd=>?_⟩
   obtain ⟨a,Y,hY,hW⟩:= h.uses c f hp w hq A u V hu; let X:= gauge a (shape (cognac A) u V)
   have hz i:= Slide.village A u i; have hv : flags P.threshold (shape (cognac A) u V)=∅:= Slide.allFlag (cognac A) u V s (fun i=> (neighbors_mem ..).2 ((hz i).trans (Nat.le_of_lt hq))) P.threshold P.threshold_pos.le hu
   have hF : flags P.threshold X=∅:= by unfold X; rw [gauge_flags,hv]
   have hy: flags P.threshold (Arc.route G β Y)=∅:=by rw [hY]; exact hF
   have hw :=Portal.Mare.valid hg Y hW hy; rw [hY] at hw
   exact Arc.vetted u (cognac A) V a (fun i=> (hz i).trans (Nat.le_of_lt hq)) (hf.smooth _ (by unfold Healthy; rw [hv]; simp)) (hh.smooth _ hu) hf.symmetry (hf.smooth X (by unfold Healthy; rw [hF]; simp)) hw l hl hd

section stationary
variable {g : Config G c→ℝ}
lemma same_air (hr : 0 ≤ R) {t:ℝ} (hP:P.Regular univ g) (hp: Portal.Mare P (g-fun _=>t) β R b):
      (0 ≤ b)∧ P.Regular univ (Boulevard.stillA g)∧ Portal.Mare P (Boulevard.stillA g) β R (b+b):= by
    let h : Config G c→ℝ:= g-fun _=> t; let H U:= h U - h 1
    have hv : ‖h 1‖ ≤ b:= by
        have ha : Arc.route G β (0:Positions (Uniform.Primary c G)) = 1:=by
            ext1 i; rw [Arc.route,smul_zero, actual,represent_link,map_zero]; simp
        have hh:=hp.valid 0 (by simpa using hr) ?_ [] (show 0 ≤ P.order from Nat.zero_le _) (by simp)
        · rw [ha] at hh; exact hh
        rw [ha]; exact smoky (by intro i; simpa [Lattice.Step.read, Gauge.chord,faceValue,square, travel,posDir,negDir] using P.threshold_pos)
    have ht:stillA g= H:=by funext i; change g i-g 1=g i-t-(g 1-t); ring
    rw [ht]; have hy: P.Regular univ h:= CouplingShape.reg_sub hP (CouplingShape.reg_const _)
    let f₁:=fun (_: Config G c)=> h 1; have hz: P.Regular univ f₁:= CouplingShape.reg_const _
    refine ⟨(norm_nonneg _).trans hv,CouplingShape.reg_sub (p:=P) hy hz,⟨fun x hx ha l hl hf=>?_⟩⟩
    let v:=Arc.route G β x; have hF : Healthy P.threshold univ v:=by unfold Healthy v; rw [ha]; simp
    have hK : ∀ x:Directions G c, ‖x‖ ≤ P.threshold → P.dirBound 0 x:= by
       intro x hx i; exact ((norm_le_pi_norm _ _).trans hx).trans (le_mul_of_one_le_right P.threshold_pos.le (one_le_pow₀ (by simp)))
    change ‖leftDerivs (h-f₁) l v‖ ≤ _
    rw [VerifiedReset.left_sub (show Local.Chart P.order h v from hy.smooth _ hF) (show Local.Chart P.order f₁ v from hz.smooth v hF) hl]; exact (norm_sub_le ..).trans (add_le_add (hp.valid x hx ha l hl hf) (((CouplingShape.sup_const (p:=P) (o:=(0:Site c)) (X:=univ) (h 1)).2 v hF l hl fun i hi=> hK _ (hf i hi)).trans hv))
end stationary

section stars
variable (Q:∀ i:Stars,(Y i).val=2*(w+i.val)) (f₀:Offer G c)(fa:∀ i:Stars,Offer G (Y i)) {q t:Stars→ℝ}
def warmth (P:BudgetPoint)(z:ℕ) (q:Stars→ℝ):= oroW P z (fun i=>q i+q i)
lemma Southern (hx:0 ≤ R)(hw:w+5 ≤ z)(hc:2*z<c.val) (h: ∀ i j, P.Regular univ (fa i j))(hρ:Arc.Deduct G P β z R)
    (hq :∀ i, Portal.Mare P (Trio.froth (fa i)-fun _=> t i) β R (q i)):
       ∀ u:Site c, let v:=Trio.ornament Q fa u; P.Regular (neighbors z u) v∧ P.supBounds u (neighbors z u) v (warmth P z q):=by
    intro u v; let x (i):= Boulevard.stillA (Trio.froth (fa i)); let g (i:Stars):= x i ∘ shape (pad Q i) u
    have hp i:P.Regular univ (Trio.froth (fa i)):=by rw [show Trio.froth (fa i)= ∑ j: Site (Y i),fa i j from funext (fun j=> (Finset.sum_apply ..).symm)]; exact Meadow.regularA _ fun j _=>h i j
    have he i:= same_air hx (hp i) (hq i); have hg i:= calibrated (x i) hρ hc (Q i).ge (show w+i.val+1≤ z from (by have h:=i.isLt; omega)) (he i|>.2.1) (add_nonneg (he i|>.1) (he i|>.1)) (he i|>.2.2) u
    unfold v; rw [Trio.orchard]; exact ⟨Meadow.regularA _ (fun i _=> CouplingShape.reg_scale _ ((hg i).1)),Trio.sup_S _ _ _ univ (neighbors z u) u (fun i _=> CouplingShape.reg_scale _ ((hg i).1)) (fun i _=>CouplingShape.sup_scale _ ((hg i).2))⟩
end stars
end YM.RemainderComparison.WickReps
