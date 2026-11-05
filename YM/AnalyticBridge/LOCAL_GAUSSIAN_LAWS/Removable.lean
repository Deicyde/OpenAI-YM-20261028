import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Rounds
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.WeakSource

/-!
# Move entry at a remote evaluation

Even curved data there use chord rate and linear pricing of frozen
transports on T.up, all in common V frame. Include stencil test as
in E (support from *input* column; no off-mask cancellation). This
invoice overpays O(span); no column sums demanded.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Remote
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Motion Rows SectorNext.Remainder.Affine Push.SectorMeasure 
open Pressure.Stores Gaussian Tree Wisps Bid
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G : Gauge} {c f n : Side} {S : StepData c f} {x : ℝ}

-- supply both arms of the •inl bound from patch estimates
lemma barrel_both (W : PathData G) {p : Clip} {σ C v : ℝ} (hW : W.Bounds p σ C v) (U : Config G f) (j : Cell f)
    (R : ℕ) (z y : LogArray G (Cell f)) {A t : ℝ} (hA : 0≤A) (ht : 0≤t)
    (h : ∀ l, let P := (W.row j.2 l).2; P.length ≤ R →
      G.chord (travel U j.1 P.walk) ≤ R*t ∧
      let i := Work.F03.slotFace P j.1
      ‖z i-y i‖ ≤ A*t ∧ ‖y i‖ ≤ A) :
    ‖barrel W R U z j-barrel W R 1 y j‖ ≤ C*(A*(1+2*G.colorScale*R)*t) ∧
      ‖barrel W R (1:Config G f) y j‖ ≤ C*A := by
  refine ⟨?_,SourceBill.barrel_max W hW _ j R y A hA (fun l hl => (h _ hl).2.2)⟩
  let P (l : ℕ) := (W.row j.2 l).2
  let c (l : ℕ) := (W.row j.2 l).1
  let i (l : ℕ) := Work.F03.slotFace (P l) j.1
  let g (a : LogArray G (Cell f)) (X : Config G f) (l : ℕ) := if (P l).length≤R then c l • G.adjoint (travel X j.1 (P l).walk) (a (i l)) else 0
  have hs a X : Summable (g a X) := barrel_summed W R X a j hW
  let X (l : ℕ) := g z U l-g y 1 l
  have hX : Summable X := (hs z U).sub (hs y 1)
  let q l := |c l| *Real.exp (σ*(P l).length)
  have hQ : SumBudget q C := hW.rows j.2
  change ‖(∑' l, g z U l)-∑' l, g y 1 l‖ ≤ _
  rw [← (hs z U).tsum_sub (hs y 1)]
  change ‖∑' l, X l‖ ≤ _
  let B:=A*(1+2*G.colorScale*R)*t
  have hS:=G.colorScale_pos
  calc
    _ ≤ ∑' l, ‖X l‖ := norm_tsum_le_tsum_norm hX.norm
    _ ≤ ∑' l, q l * B := hX.norm.tsum_le_tsum (fun l => ?_) (hQ.2.1.mul_right _)
    _ ≤ _ := by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hQ.2.2 (by unfold B; positivity)
  unfold X g; split
  next hl =>
    have hx : |c l| ≤ q l := le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg hW.width.le (by positivity)))
    rw [← smul_sub,norm_smul,Real.norm_eq_abs]
    refine mul_le_mul hx ?_ (norm_nonneg _) (hQ.1 _)
    obtain ⟨hk,h₁,h₂⟩ := h l hl
    let w:=travel U j.1 (P l).walk; let u:=y (i l)
    rw [unit_walk G]
    have hv := ad_change u w 1
    rw [inv_one,mul_one] at hv
    rw [show G.adjoint (travel _ _ _) (z (i l))-G.adjoint (1:G.El) _ =
        G.adjoint w ((z (i l))-u)+(G.adjoint w u-G.adjoint 1 u) from (by rw [map_sub]; abel)]
    refine (norm_add_le ..).trans ?_; rw [G.norm_adjoint]
    refine (add_le_add h₁ hv).trans ((add_le_add_right (?_ : 2*G.colorScale*G.chord w*‖u‖ ≤ 2*G.colorScale*((R:ℝ)*t)*A) (A*t)).trans_eq ?_)
    · exact mul_le_mul (mul_le_mul_of_nonneg_left hk (by positivity)) h₂ (norm_nonneg _) (by positivity)
    unfold B; ring
  rw [sub_self,norm_zero]; apply mul_nonneg (hQ.1 _); unfold B; positivity

def aim (S : StepData c f) (i : Slots S) := i.1.act (roots S (i.2.elim (fun j => .inl j.1) Sum.inr))

set_option maxHeartbeats 380000 in
theorem pulse_bill (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (C : ℝ) (hp : P.Branches K G) (hC : 0 ≤ C) :
    ∃ A δ : ℝ, 0≤A ∧ 0<δ ∧ ∀ t : ℝ, 0≤t → t ≤ δ → ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K →
    ∀ (T : Tube G S) (Λ σ : ℝ), T.high=p → T.up.Bounds p σ C Λ → ∀ (x : ℝ) (o : Site c) (D : ℕ) (V : Config G c),
    paid S (replica S.ratio V) o D t → ∀ (a : Directions G f), ‖a‖ ≤ 1 → invoice S a o D →
    ∀ (k:S.Choices) (i : Slots S), separation o (aim S i)+span P x ≤ D →
      ‖bump T x V k a i-bump T x (1:Config G c) k a i‖ ≤ A*(1+(till x:ℕ))*t ∧ ‖bump T x (1:Config G c) k a i‖ ≤ A := by
  obtain ⟨A,δ,hA,hδ,H⟩ := remote_authorized G P K hp
  let c:=G.colorScale; have hc : 0<c := G.colorScale_pos
  let e := Real.sqrt p.direct; let f' := Real.sqrt K.penalty
  have hf : 0≤f' := Real.sqrt_nonneg _; have he : 0≤e := Real.sqrt_nonneg _
  let B:= (1+C*(1+2*c)+e+f')*A
  have hb : 0 ≤ B := by unfold B; positivity
  have hv : C*A*(1+2*c)≤B := by unfold B; nlinarith
  have hxC : C*A≤B := (le_mul_of_one_le_right (mul_nonneg hC hA) (show 1≤1+2*c by linarith)).trans hv
  have hxE : e*A≤B := by unfold B; nlinarith [mul_nonneg hC (show 0 ≤ 1+2*c by linarith)]
  have hxF : f'*A≤B := by unfold B; nlinarith [mul_nonneg hC (show 0 ≤ 1+2*c by linarith)]
  refine ⟨B,δ,hb,hδ,?_⟩
  intro t ht ht' c' f S HS HK T Λ σ H' HΛ x o D V Hw a ha hi k i Hsep
  let r : ℝ := (till x:ℕ); have hR : 0≤r := Nat.cast_nonneg _
  obtain ⟨s,j|i⟩ := i
  · change separation o (s.act (S.ratio.parent j.1.1)) + _ ≤ _ at Hsep
    change ‖faceKick T x V a s j-faceKick T x 1 a s j‖ ≤ _ ∧ ‖faceKick T x 1 a s j‖ ≤ _
    have hh (z : Cell f) (h : separation o (s.act (S.ratio.parent z.1))+5≤D) := (H t ht ht' S HS HK o D V s a Hw hi).1 z h
    unfold faceKick; split
    next hb' =>
      rw [fixed_facade,fixed_facade,replica_one,show pull s 0 (1:Config G f)=1 from (by funext i; rw [turn_read]; split <;> simp)]
      obtain ⟨H1,H2⟩ := barrel_both T.up HΛ (pull s 0 (replica S.ratio V)) j.1 (till x) (fun z => plaquetteJet S V s z a)
        (fun z => plaquetteJet S (1:Config G c') s z a) hA ht (by
          intro l W hl
          have hr : W.walk.length≤till x := by unfold Slot.length at hl; omega
          refine ⟨(travels_paid s ht Hw j.1.1 W.walk ?_).trans (by gcongr),?_⟩
          · unfold span at Hsep; omega
          intro p'
          obtain ⟨H1,H2⟩ := hh p' (by
            have hv := slot_distance (S:=S) W j.1.1
            have h : separation (s.act (S.ratio.parent j.1.1)) (s.act (S.ratio.parent p'.1))≤till x := (separation_signed ..).le.trans (hv.trans hr)
            unfold span at Hsep
            have := separation_triangle o (s.act (S.ratio.parent j.1.1)) (s.act (S.ratio.parent p'.1)); omega)
          exact ⟨H1.trans (mul_le_of_le_one_right (mul_nonneg hA ht) ha),H2.trans (mul_le_of_le_one_right hA ha)⟩)
      refine ⟨H1.trans ?_,H2.trans hxC⟩
      change C*(A*(1+2*c*r)*t)≤_
      calc
        _ ≤ C*A*(1+2*c)*(1+r)*t := by rw [show C*(A*(1+2*c*r)*t)=C*A*(1+2*c*r)*t by ring,mul_assoc (C*A) (1+2*c)];
                                                    gcongr; nlinarith
        _ ≤ _ := by gcongr
    rw [← smul_sub,norm_smul,norm_smul,H',Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    obtain ⟨hx,hy⟩ := hh j.1 (by unfold span at Hsep; omega)
    refine ⟨(mul_le_mul_of_nonneg_left (hx.trans (mul_le_of_le_one_right (mul_nonneg hA ht) ha)) he).trans ?_,
      (mul_le_mul_of_nonneg_left (hy.trans (mul_le_of_le_one_right hA ha)) he).trans hxE⟩
    change e*(A*t)≤B*(1+r)*t; rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ ht; nlinarith
  change separation o (s.act i.1)+_≤_ at Hsep
  change ‖noiseKick V k a s i-noiseKick (1:Config G c') k a s i‖≤_ ∧ ‖noiseKick (1:Config G c') k a s i‖≤_
  obtain ⟨he,hv⟩ := (H t ht ht' S HS HK o D V s a Hw hi).2 k i (by unfold span at Hsep; omega)
  unfold noiseKick; rw [neg_sub_neg, ← smul_sub,norm_smul,norm_neg,norm_smul,HK,Real.norm_of_nonneg (Real.sqrt_nonneg _),norm_sub_rev]
  refine ⟨(mul_le_mul_of_nonneg_left (he.trans (mul_le_of_le_one_right (mul_nonneg hA ht) ha)) hf).trans ?_,
    (mul_le_mul_of_nonneg_left (hv.trans (mul_le_of_le_one_right hA ha)) hf).trans hxF⟩
  change f'*(A*t)≤B*(1+r)*t; rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ ht; nlinarith
end YM.AnalyticBridge.LocalGaussianLaws.Remote
