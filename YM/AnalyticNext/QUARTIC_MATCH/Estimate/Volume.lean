import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Junction

/-! # Pre-L centered frame prices. Respect w and objective. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Estimate
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Work.F03 YM.Next.Free Work.F08 Pre.Knot
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
attribute [local instance] Gauge.frobInner
namespace Yard
open Purse Logfee
variable {G : Gauge} {c f : Side} (S : StepData c f) {ι : Type} [DecidableEq ι]
local notation "Y" => S.patch.Points
local notation "X" => Dir G f
local notation "E" => G.Mat

section amount
variable {A B γ : Type*} [Fintype γ] [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
omit [DecidableEq ι] in
lemma funds_more (a : γ→ A→B) {x} (h : ∀ i,ContDiffAt ℝ ω (a i) x) (T : Finset ι) (d) (w : γ→ℝ) :
    bill T d (fun y => ∑ i,w i • a i y) x=∑ i,w i • bill T d (a i) x := by
  change bill T d (fun y => ∑ i,(w i • a i) y) x=_
  rw [sum_bill Finset.univ T d (fun i => w i • a i) x (fun i _ => (h i).const_smul (w i))]; simp_rw [smul_price T d (h _)]
end amount
omit [DecidableEq ι] in
lemma starWeighted (h : S.patch.Branches S.kernel G) (a : S.SitesChoice) (t : Finset ι) (v : ι→X) (i : Site c) (ht : t.Nonempty) :
    ∑ j : Y, S.patch.weight j • G.lie.starProjection (bill t v (envelope S a i j) 0)=0 := by
  let L := G.lie.starProjection
  have he : (fun x => L (∑ j,S.patch.weight j • envelope S a i j x)) =ᶠ[𝓝 (0:X)] fun _ => L 1 := mass S h a i
  have hh (j) := honest S h a i j
  let f (x : X) := ∑ j, S.patch.weight j • envelope S a i j x
  have hy : ContDiffAt ℝ ω f 0 := ContDiffAt.sum fun j _ => (hh j).const_smul _
  calc
    _ = L (∑ j : Y, S.patch.weight j • bill t v (envelope S a i j) 0) := by simp only [L,map_sum,map_smul]
    _ = L (bill t v f 0) := by rw [show bill t v f 0=_ from funds_more _ hh t v S.patch.weight]
    _ = _ := (left_price t v L hy).symm.trans ((Estimate.germ he).trans (mute ht v 0 _))

lemma heaps (G : Gauge) (n j : ℕ) (η : ℝ) (hp : 0<η) : ∃ C : ℝ,0 ≤ C ∧
    ∀ (ι : Type) [DecidableEq ι] (c f : Side) (S : StepData c f) (a : S.SitesChoice),S.patch.J=j →
    S.patch.Branches S.kernel G → ∀ (P : Purse ι (Site f)) (v : ι→Dir G f), tollRate P S.patch.L η →
    P.cap=(S.patch.L.val:ℝ)^2 → Linkbill S.patch.L P v → ∀ t : Finset ι,t.card ≤ n →
    (cap S P).Many t v (envelope S a) 0 C := by
  induction n with
  | zero =>
    refine ⟨‖(1:G.Mat)‖,norm_nonneg _,?_⟩
    intro ι _ c f S a _ hb P v _ _ _ t ht
    rw [Nat.le_zero,Finset.card_eq_zero] at ht; subst t; unfold Many; simp_rw [blank,anchored S hb a]
    exact Spend.blank (norm_nonneg _) (fun i j => le_rfl)
  | succ n ih =>
    have hd : ContDiffAt ℝ ω (penny G) (1:G.Mat) := G.focus_diff
    obtain ⟨C,hC,he⟩ := ih
    let D := sea j n G η C
    let r := sea j (n+1) G η C
    obtain ⟨E',hE,H⟩ := leftover (penny G) (1:G.Mat) hd n D (sea_pos j n G η hC)
    let K := r+E'
    refine ⟨max C (K+pScale j*K),le_trans hC (le_max_left ..),?_⟩
    intro ι _ c f S a hv hh P v hl hp' hL z hz
    rcases Nat.eq_or_lt_of_le hz with hs|hs
    · let b := tape S a (G:=G)
      let q := n+1
      have hG (x k) : ContDiffAt ℝ ω (b x k) 0 := stamped S hh a x k
      have Hh (U : Finset ι) (hu : U.card ≤ n) := he ι c f S a hv hh P v hl hp' hL U hu
      have hg s (_ : s⊆z) (hs : s.card ≤ n) : (cap S P).Many s v b 0 D := by
        unfold D; rw [← hv]; exact tote S hh a hp P v hl hp' hL s n hs (fun T ht => Hh _ ((Finset.card_le_card ht).trans hs))
      let Q := cap S P
      let R : Site c → S.patch.Points→G.Mat := fun x k => bill z v (envelope S a x k) 0
      let G' x k := bill z v (b x k) 0
      let A (x : Site c) := avg (R x); let L := G.lie.starProjection
      let Y' : Site c→S.patch.Points→G.Mat := fun x y => R x y - L (A x)
      have hQ : Q.Spend z (fun x y => G' x y-A x) r := by
        unfold r; rw [← hv]; exact compensate S hh a hp P v hl hp' hL z hs hC (fun U _ => Hh U)
      have Hq := H ι _ _ _ b _ _ Q z hs hG (swept S hh a) hg
      have hy : Q.Spend z Y' K := by
        have hc := hQ.change (g:=fun x y => L (G' x y - A x)) (fun x y => G.lie.norm_starProjection_apply_le ..)
        refine (hc.plus Hq).change fun x y => ?_
        simp only [Pi.add_apply]
        have he' : R x y=bill z v (penny G ∘ b x y) 0 := Estimate.germ (splices S hh a x y)
        have He : bill z v (penny G ∘ b x y) 0 - fderiv ℝ (penny G) 1 (bill z v (b x y) 0)=R x y - L (G' x y) :=
          congr_arg₂ (·-·) he'.symm (DFunLike.congr_fun G.focus_deriv.hasFDerivAt.fderiv (G' x y))
        apply le_of_eq; refine Eq.symm ( (congr_arg (‖·‖) ((congr_arg (L (G' x y-A x)+·) He))).trans ?_)
        rw [map_sub]; unfold Y'
        rw [show L (G' x y)-L (A x)+(R x y-L (G' x y))=R x y-L (A x) by abel]
      have ha' := (hy.change (g:=fun x j => L (Y' x j)) fun i j => G.lie.norm_starProjection_apply_le _).heavy
        S.patch.weight S.patch.weight_sum S.patch.weight_nonneg (pScale_ge j) (hv ▸ earn S)
      have hz y : L (A y) = -(∑ x,S.patch.weight x • L (Y' y x)) := by
        have hp : L (L (A y))=L (A y) := G.lie.starProjection_eq_self_iff.mpr (G.lie.starProjection_apply_mem _)
        have hT : ∑ x,S.patch.weight x • L (R y x)=0 := starWeighted S hh a z v y (Finset.card_pos.mp (by omega))
        simp_rw [Y', map_sub,hp,smul_sub,Finset.sum_sub_distrib,hT,← Finset.sum_smul,S.patch.weight_sum,one_smul, zero_sub,neg_neg]
      have ht := energize (β:=S.patch.Points) ha'.neg
      apply ((hy.plus ht).mono (le_max_right ..)).change
      intro x y
      rw [show (Y'+_) x y=Y' x y+L (A x) from congr_arg (Y' x y + ·) (hz x).symm]
      unfold Y'; rw [sub_add_cancel]
    exact (he ι c f S a hv hh P v hl hp' hL z (by omega)).mono (le_max_left ..)
end Yard
end YM.AnalyticNext.QuarticMatch.Estimate
