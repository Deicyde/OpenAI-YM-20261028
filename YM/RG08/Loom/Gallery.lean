import YM.RG08.Loom.Stars
/-!
# Following actual footprints in the auxiliary finite-period proof:
No constants fall out by separate evaluation history
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Loom
open Function Filter Lattice Wilson Exterior Bloch Next.Free Work.F08 RG Laurent Precision Finset
open Quire Stationary Scores Matrix PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Shade Reflect Analysis MeasureTheory PertExtension.GaussianScore Tree FreeResolvent Profiles PertExtension.Chart
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {p c f : Side} (S : StepData c f) (G : Gauge) (T : Forest S.ratio)
variable {M : Matrix (Body 1 f) (Body 1 c) ℝ} {v w : ℝ→Link G c} {n h j τ e : ℕ} {k : KernelChoices} {D : ℕ}{R : ℝ} {φ φ' : Exam D}
variable {U U' H H' : BoardU D R G} {V : ℕ→ Config G f→ℝ}{F F' : Air G} {W W' : Site S.ratio.count → ℕ→Config G f→ℝ} {B K : FreeResolvent.FaceRow} {σ : ChartRatio G} {o o' : Site c} {κ : S.Choices} {i : G.ColorIndex}
local notation "Ξ" => treeMatrix G S T K
local notation "Σ'" => surge S G F i σ
local notation "E₀" => expEra Σ'
local notation "W_[" U "," φ "," p "]" => (fun k l=>plug (Scores.Pages.roll (spinner p) (S.ratio.count.val:ℝ)⁻¹ φ) R ∘ U k l)
local notation "z_[" o "," j "]" => (S.ratio.assemble (o,j))
local notation "A" => T.Slice G

-- variant of Reflect.incline; require two weightsings on SAME s' hole-free.
lemma twice_incline {X : Type} [TopologicalSpace X] {a : X} {u v : Set X}(hu : u ∈ 𝓝 a)(hv : v∈𝓝 a) (g : ℝ→ (X≃ₜX))
    (hp : Tendsto (fun p:ℝ×X=>g p.1 p.2) (𝓝 (0,a)) (𝓝 a))
    (he : Tendsto (fun p:ℝ×X=> (g p.1).symm p.2) (𝓝 (0,a)) (𝓝 a))
    (B:ℝ×X→Prop)(hb : ∀ᶠ p:ℝ×X in 𝓝 (0,a),B p) :
    ∃ s ∈ 𝓝 a,s ⊆ u ∧ IsOpen s ∧ (∀ᶠ i in 𝓝[>]0,g i '' s ⊆ v ∧ ∀ x∈s,B (i,x)) ∧ ∃ z∈𝓝 a,∀ᶠ i in 𝓝[>]0,z⊆g i '' s := by
  let f (i:ℝ)(x:X):= if B (i,x) then (0:ℝ) else 1
  obtain ⟨s,hx,hU,hS,H,hT⟩:=Reflect.incline _ _ hu hv g hp he f (fun _ _=>0) (hb.mono fun i hi=>if_pos hi)
  exact ⟨s,hx,hU,hS,H.mono (fun i hh=> ⟨hh.1,fun x hx=> by simpa [f] using hh.2 x hx⟩),hT⟩

structure WalkPays (g : ℝ→((A)≃ₜ(A))) (κ : S.Choices) (n h τ : ℕ) (v w:ℝ→ Link G c)(V : ℕ→Config G f→ℝ)(W W' : Site S.ratio.count→ℕ→Config G f→ℝ) : Prop where
   sunrise : Tendsto (fun p:ℝ×A=>g p.1 p.2) (𝓝 (0,1)) (𝓝 1)
   return_t : Tendsto (fun p:ℝ×A=> (g p.1).symm p.2) (𝓝 (0,1)) (𝓝 1)
   mass : ∀ t,MeasurePreserving (g t) (T.order G) (T.order G)
   day : ∀ᶠ p:ℝ×A in 𝓝 (0,1), discPay S G T v κ n V p.1 p.2=discPay S G T w κ n V p.1 (g p.1 p.2) ∧
       chapel G S n W τ h p.1 (T.drape p.2)= chapel G S n W' τ h p.1 (T.drape (g p.1 p.2)) -- numerical order explicit.
-- notation syntax consumed
set_option maxHeartbeats 500000 in
theorem carrying (HP : LocalRatio σ)(hK : S.patch.Branches S.kernel G)
    (hX : Inputs S M (K.acts f) (B.acts c))(hk : Whole K)(hb : Whole B)(he : ∀ m,(K.acts m).IsSymm)(hg : ∀ m,(B.acts m).IsSymm) (hΔ : (Ξ).PosDef)
    (hV : ∀ i,Caper (quad G (YM.RG08.hessian K)) F n i (V i)) (hF:Gets F) (ht:Halt F)
    (hY : ∀ w : Link G c, Aura (fun j=> leaned hΔ (snow G T) (chargeS S T G) (lodgeP G S.ratio (riseM S G T M *ᵥ w) w) (E₀ j)) (fun j=> -grand (j+2) (F' j) c w))
    (hW : ∀ p j,Cargo z_[o,p] τ j (n+τ) W_[U,φ,p] (W p j)) (hx : ∀ p j,Cargo z_[o',p] τ j (n+τ) W_[H,φ',p] (W' p j))
    (hu : ∀ i j,Pens (U i j)) (hU' : ∀ i j,Pens (H i j)) (hR:1/2≤R)
    (hZ : ∀ w : Link G c, let P := leaned hΔ (snow G T) (chargeS S T G) (lodgeP G S.ratio (riseM S G T M *ᵥ w) w); ∀ j,P (billow (valve G U S φ h τ o) E₀ j)=∑ b∈wheel j, large o (τ+b.1) (fun r=> plug φ R ∘ U' b.1 r) w*P (E₀ b.2))
    (hh : ∀ w : Link G c, let P := leaned hΔ (snow G T) (chargeS S T G) (lodgeP G S.ratio (riseM S G T M *ᵥ w) w); ∀ j,P (billow (valve G H S φ' h τ o') E₀ j)=∑ b∈wheel j, large o' (τ+b.1) (fun r=> plug φ' R ∘ H' b.1 r) w*P (E₀ b.2))
    (g : ℝ→ ((A)≃ₜ(A))) (hN : AnalyticAt ℝ v 0) (hL : AnalyticAt ℝ w 0) (hw : WalkPays S G T g κ n h τ v w V W W') :
    Fit (n+1) (fun t=> t^τ*arco c (fun j=> large o (τ+j) (fun r=> plug φ R ∘ U' j r)) v n t)
        (fun t=> t^τ*arco c (fun j=> large o' (τ+j) (fun r=> plug φ' R ∘ H' j r)) w n t) := by
  obtain ⟨v',ha,htv⟩:= linings hN.contDiffAt; obtain ⟨w',hs,hr⟩:= linings hL.contDiffAt
  obtain ⟨x,hxv,hy⟩:= evoked S G T M v' n h K B σ F V W τ o U φ κ i HP (hN.congr htv.symm|>.contDiffAt) hK ha hV hF ht hk hb he hg hX hΔ F' hY hW hu hR U' hZ
  obtain ⟨d,hdv,hD'⟩:= evoked S G T M w' n h K B σ F V W' τ o' H φ' κ i HP (hL.congr hr.symm|>.contDiffAt) hK hs hV hF ht hk hb he hg hX hΔ F' hY hx hU' hR H' hh
  have hm : ∀ᶠ p:ℝ×A in 𝓝 (0,1), chargeDensity S G T v' n h V W τ κ p.1 p.2=chargeDensity S G T w' n h V W' τ κ p.1 (g p.1 p.2) ∧ discPay S G T v' κ n V p.1 p.2= discPay S G T w' κ n V p.1 (g p.1 p.2) := by
    filter_upwards [hw.day,(continuous_fst.tendsto ((0:ℝ),(1:A))).eventually htv, (continuous_fst.tendsto ((0:ℝ),(1:A))).eventually hr] with p hp hv ht
    have hv : discPay S G T v' κ n V p.1 p.2=discPay S G T w' κ n V p.1 (g p.1 p.2) := by unfold discPay; rw [hv,ht]; exact hp.1
    exact ⟨congr_arg₂ (· * ·) hp.2 hv,hv⟩
  obtain ⟨s,hS,hI,hJ,hp,hG⟩:= twice_incline hxv hdv g hw.sunrise hw.return_t _ hm
  have h := hy (fun _=>s) (Eventually.of_forall fun t=>⟨hJ.measurableSet,hI⟩) ⟨s,hS,Eventually.of_forall fun t=>le_rfl⟩
  have ht' := hD' (fun t=>g t '' s) (hp.mono fun i hi=>⟨((g i).isOpenMap s hJ).measurableSet,hi.1⟩) hG
  have hD : Fit (n+1) (fun t=>t^τ*arco c (fun j=>large o (τ+j) (fun r=> plug φ R ∘ U' j r)) v' n t) (fun t=>t^τ*arco c (fun j=> large o' (τ+j) (fun r=>plug φ' R ∘ H' j r)) w' n t) := by
    apply h.turn.join; apply Fit.join _ ht'; apply Fit.supply; filter_upwards [hp] with t H
    exact congr_arg₂ (· / ·) (kohler (g t) (T.order G) (hw.mass t) _ hJ _ _ (fun i hi=> (H.2 i hi).1)) (kohler (g t) (T.order G) (hw.mass t) _ hJ _ _ (fun i hi=> (H.2 i hi).2))
  refine Fit.join (Fit.supply ?_ _) (Fit.join hD (Fit.supply ?_ _))
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds htv] with i hi; simp [arco,year,hi]
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hr] with i hi; simp [arco,year,hi]

-- Truncate AFTER conservation. Courtesy lemma
lemma minor (F : ℕ→ℝ→ℝ) (hv : ∀ i, Bill 0 (F i)) (he:j≤n): Fit (j+1) (year F n) (year F j) := by
  let f (i:ℕ) t := t^i * F i t
  have ht k: year F k=∑ i∈range (k+1), f i := funext fun t=> Eq.symm (Finset.sum_apply t ..)
  rw [ht,ht]; unfold Fit; rw [← Finset.sum_sdiff (f:=f) (show range (j+1) ⊆ range (n+1) from range_mono (by omega)),add_sub_cancel_right]; exact bill_sum _ _ (fun i hi=> bill_mul (k:=j+1) (j:=0) (ruler _ _ (by have h := mem_sdiff.mp hi|>.2; simp only [mem_range,not_lt] at h; omega)) (hv i)) -- order?
lemma licensed {x y : ℕ→ℝ→ℝ} (hx : ∀ i,Bill 0 (x i))(hy : ∀ i,Bill 0 (y i))(h : n=τ+j)(he:Fit (n+1) (fun t=> t^τ * year x n t) (fun t=>t^τ * year y n t)) : Fit (j+1) (year x j) (year y j) := by
  have H:= (minor x hx (show j≤n by omega)).turn; have hv:=minor y hy (show j≤n by omega)
  apply H.join; apply Fit.join _ hv
  have hT:= Fit.shorten (f:=fun t=>t^τ*year x n t) (g:=fun t=>t^τ*year y n t) (n:=j+1) (k:=τ) (by rw [show j+1+τ=n+1 by omega]; exact he)
  exact (Fit.supply (eventually_pos.mono fun t ht=> Eq.symm (mul_div_cancel_left₀ _ (pow_pos ht _).ne')) _).join (hT.join (Fit.supply (eventually_pos.mono fun t ht=> mul_div_cancel_left₀ _ (pow_pos ht _).ne') _))
end YM.RG08.Loom
