import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.RootCap

/-!
# All-sector affine b, mean invoices

Accounts for actual fixed-L bound for log/chart change `s=s_g`. Does not
fund stationary part of à_far. Uses fixed Ksh log cutoff for frozen inputs;
broad cap on green calls can be calibrated later with these ν estimates. Hess
locality through Posts not proved by inverse alone!
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat 
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {ι κ : Type*} {L : Side}

lemma color_cover {A : ℝ} (he : 0≤A) (z : G.Color) (h : ∀ j,|z j|≤A) : ‖z‖ ≤ (Fintype.card G.ColorIndex)*A := by
  apply le_of_sq_le_sq _ (by positivity); rw [EuclideanSpace.real_norm_sq_eq]; refine le_trans (b:= ∑ _j : G.ColorIndex,A^2) ?_ ?_
  · exact sum_le_sum fun j _ => by rw [← sq_abs]; gcongr; exact h j
  rw [sum_const,nsmul_eq_mul,mul_pow, card_univ]; gcongr
  exact_mod_cast (show Fintype.card G.ColorIndex ≤ (Fintype.card G.ColorIndex)^2 by nlinarith)

lemma invoice [Fintype κ] {M : Matrix ι κ ℝ} {a : ι → Site c} {b : κ → Site c} {r C K : ℝ}
    (h : Rows a b M r C) (he : 0 ≤ r) (i : ι) (v : κ → ℝ) (hv : ∀ i, |v i| ≤ K) (hK : 0≤K) :
    |(M *ᵥ v) i| ≤ C*K := by
  unfold Matrix.mulVec dotProduct
  apply (abs_sum_le_sum_abs ..).trans
  refine (Finset.sum_le_sum (g:=fun j=> |M i j| * K) fun j _ => ?_).trans ?_
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _)
  rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (pure_pay h he i) hK

namespace Coat
variable (X : Coat T F)

lemma valent (A : ℝ) (hA : 0 ≤ A) (M : ℝ) (hm : ∀ V, Bid.Maximum M T X.x V) (hM : 0<M) (hg : X.manifest)
    {W γ C : ℝ} (hC : 0 < C) (hR : Room P S T X.x) (hs : ShellAccess S G X.x W X.width γ)
    (h : Bounded T P.top.width C) (hc : ∀ (V : Config G c) (k : S.Choices) (p : Rod c f), Clean V X.x (focus S p) X.B →
      ‖baseStroke T X.x k V p‖ ≤ A*X.t) (i : Mention c f) :
    ‖X.priced 0 i‖ ≤ scale*((A+M)*X.t+C*(γ*(2*(X.width*X.t)))) := by
  have hp := hs.log
  have hk : 0 ≤ γ*(2*(X.width*X.t)) := mul_nonneg hp.price.le (mul_nonneg (by norm_num) hp.down.le)
  have hh : 0<X.t := hR.fiery
  unfold priced; split
  next he =>
    let s := i.1; let V := pull s 0 X.V; let p := i.2
    unfold realPath; rw [norm_smul,Real.norm_of_nonneg scale_pos.le, signal,lens_zero,add_zero]
    apply mul_le_mul_of_nonneg_left _ scale_pos.le
    apply (norm_add_le ..).trans
    have hz : ‖X.saved‖ ≤ γ*(2*(X.width*X.t)) := (pi_norm_le_iff_of_nonneg hk).mpr (X.saved_cost hs)
    have hZ := (oriented_cap hC h X.V s p X.R X.saved).trans (mul_le_mul_of_nonneg_left hz hC.le)
    apply add_le_add _ hZ; unfold request
    apply (norm_sub_le ..).trans
    rw [add_mul]; apply add_le_add _ (paysGuide _ hM.le V (hm V))
    refine hc _ _ _ (Clean.turn ?_)
    have hi : Clean X.V X.x (s.act (focus S p)) (6*X.B) := clean_far X.seeds X.V hg (by rwa [cost_is_here])
    exact hi.shrink (by dsimp only [p,s] at *; rw [separation_self]; omega)
  next he => rw [norm_zero]; have := scale_pos; positivity

/-- Prepare η := -g^{-1}(Aμ+b): b paid at all sectors, orientation-
total bills. -/
lemma freedom {X : Coat T F} {L : Side} {η r Q Y C : ℝ} (h : Rotator P L η r Q Y X)
    (hC : 0≤C) (hp : ∀ i, ‖X.priced 0 i‖ ≤ C) :
    let m := Census.tubularPrice G L;
    let b := Y*C; let P' := payE η r Q m; let d := distPay η r Q m X.B
    (∀ i, |X.linearBill i| ≤ b ∧ |X.driftM i| ≤ P'*b) ∧ (∀ i, ‖X.μ i‖≤ Fintype.card G.ColorIndex * (P'*b)) ∧
      ∀ i, |(X.plate *ᵥ X.driftM + X.linearBill) i| ≤ Q*d*b := by
  intro m b P' d
  let V := X.kernelA; let v := X.linearBill; let k := retain η r Q
  let A := X.plate
  have hg i : |v i| ≤ b := invoice h.matrix.2 h.full.hot.le i _ (fun i => (stand_cap ..).trans (hp _)) hC
  have ht : 0 ≤ P' := h.scale.disc
  have he : 0 ≤ b := mul_nonneg h.signs.le hC
  have hv : 0 < k := h.full.prices
  have hu i : |X.driftM i| ≤ P'*b := by
    unfold driftM; rw [Pi.neg_apply,abs_neg]; exact invoice (h.scale.primal _).2 (show 0 ≤ 2*k by positivity) _ _ hg he
  refine ⟨fun i=> ⟨hg i, hu i⟩, fun i => color_cover (mul_nonneg ht he) _ (fun j => hu (i,j)),?_⟩
  intro i
  have hx := flipped (h.scale.breach X.shutter)
  have hs : A⁻¹.IsHermitian := h.scale.symmetry.inv
  have hI : A⁻¹.transpose=A⁻¹ := by rw [← show (A⁻¹)ᴴ=A⁻¹.transpose from by ext; simp,hs.eq]
  have hh := paid_mul h.scale.relented hx hv.le h.scale.fuel.le (mul_nonneg ht (h.scale.heap _))
  have hk : X.plate *ᵥ X.driftM+X.linearBill=-((A*(V-A⁻¹).transpose) *ᵥ v) := by
    change A *ᵥ (-(V.transpose *ᵥ v))+v=_; rw [transpose_sub,hI,mul_sub,h.scale.initial.1,
      Matrix.sub_mulVec,Matrix.one_mulVec, Matrix.mulVec_neg, Matrix.mulVec_mulVec]; abel
  rw [hk,Pi.neg_apply,abs_neg]; exact invoice hh.1 hv.le _ v hg he

/-- η ordered COST in unscaled mean and residual; constants can be used
without enlarging any fixed-L exponent targets. -/
theorem dividend (P : Teller G) (L : Side) (D : Patch) (hd : D.Branches P.bind G)
    (η r Q Y W γ K : ℝ) (hη : Torch η r Q) (k : ℝ) : ∃ C : ℝ, 0<C ∧ ∃ E : ℝ→ℝ,
      Rate G L k E ∧ ∀ᶠ x in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio)
      (X : Coat T F), X.x=x → X.width=K → S.patch=D → S.patch.L=L → Rotator P L η r Q Y X → X.manifest →
      ShellAccess S G x W K γ →
        (∀ i, ‖X.priced 0 i‖ ≤ C*X.t) ∧ (∀ i, |X.linearBill i| ≤ C*X.t) ∧ (∀ i, ‖X.μ i‖ ≤ C*X.t) ∧
        ∀ i, |(X.plate *ᵥ X.driftM+X.linearBill) i| ≤ E x := by
  obtain ⟨A,hA,H₁⟩ := crowns P D hd L
  obtain ⟨M,U,hM,hU,H₂⟩ := max_prices P
  obtain ⟨N,hN,H⟩ := bounded_stencils P D hd
  let m := Census.tubularPrice G L
  let B x := radiusB x
  let b₁ := scale*(A+M+N*γ*(2*K))
  let b := Y*b₁
  let C₀ := payE η r Q m
  let u := (Fintype.card G.ColorIndex:ℝ)*(C₀*b)
  let C := 1+max (max (max b b₁) u) 0
  have hv : 0<C := add_pos_of_pos_of_nonneg zero_lt_one (le_max_right ..)
  let E x := Q*distPay η r Q m (B x)*(b * Pressure.fiery G x L)
  have hp : Rate G L k E := by
    convert ((((hη.physical G L (k+1/2) m).mul_left C₀).mul_left Q).mul (Rate.flame.mul_left b)) using 1
    linarith
    rfl
  refine ⟨C,hv,E,hp,?_⟩
  filter_upwards [H₁,H₂ L] with x hx hg c f S T F X he hr hS hL θ hi Hsh
  subst x
  have Hs := Hsh; rw [← hr] at Hs
  let t := X.t
  have hf : 0<t := θ.room.fiery
  have hh := hg c f S T ⟨θ.room.accepted,hL,θ.room.buys⟩
  have hu i : ‖X.priced 0 i‖ ≤ b₁*t := (X.valent A hA.le M (fun V => (hh.2 V).1) hM hi
    hN θ.room Hs (H c f S T hS θ.room.accepted) (hx c f S T hS hL θ.room) i).trans_eq (by rw [hr]; unfold b₁ t; ring)
  have hb : 0≤ b₁*t := by
    unfold b₁
    have hs := Hs.log; have hh : 0<K*t := hr ▸ hs.down; have he := pos_of_mul_pos_left hh hf.le
    have := hs.price; have := scale_pos; positivity
  let H' := freedom θ hb hu
  have hK (f : ℝ) (h : f≤max (max b b₁) u) : f*t≤C*t := mul_le_mul_of_nonneg_right
    (h.trans ((le_max_left ..).trans (le_add_of_nonneg_left (by norm_num)))) hf.le
  refine ⟨fun i => (hu i).trans (hK _ ((le_max_right ..).trans (le_max_left ..))), fun i => ((H'.1 i).1.trans
    ((by rw [← mul_assoc] : Y*(b₁*t) ≤ b*t).trans (hK b ((le_max_left ..).trans (le_max_left ..))))),fun i => ?_,fun i => ?_⟩
  · apply (H'.2.1 i).trans
    apply le_trans _ (hK _ (le_max_right _ u)); unfold u C₀ b m; exact le_of_eq (by ring)
  apply (H'.2.2 i).trans_eq; unfold E b B m t Coat.B Coat.t; rw [hL]; ring
end Coat
end YM.ConnectedActivityE6
