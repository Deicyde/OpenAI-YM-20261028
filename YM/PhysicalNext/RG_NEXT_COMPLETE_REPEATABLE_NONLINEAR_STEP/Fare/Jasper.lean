import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Fare.Diap
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Fare.Ole

/-! # Exponential tail corollary on outside (ONLY pure with healthy measure)
 Chart branch gap & volume W monitor. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Fare
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio) (T : Tube G S) (k : S.Choices)
    {u v p σ C Λ : ℝ} {n : ℕ}
local notation "X" => Positions (Uniform.Primary c G)
local notation "K" => Precision.Key F G
local notation "Y" => Poll.Body K
variable (A : Push.Uniform.Before G σ C S.patch.J S.kernel (n+3)) (ρ : Bid.Dir G c→ AxisChart G F) (O : ChartRatio G) (B : BudgetPoint) (β : ℝ)
local notation "R" => A.tables T.high S.patch
local notation "φ" => Lapis.table F k T.up T.high
local notation "g" => Lapis.orbit F ρ
local notation "M" => Lapis.gram F T.up T.high ρ k
local notation "ψ" => Lapis.mist F O T.up
local notation "V" => (fun x:X=>represent (tint G _ x))
local notation "G₀" => gStep β
local notation "π'" => prefactor S G β
variable (he : A.Service F T.high T.up ρ) (ha : Larger (G:=G) S) (h : T.up.Bounds T.high σ C Λ) (W : ℝ)
    (hv : 1 ≤ W) (hV : (Fintype.card (Joint F G):ℝ) ≤ W) (hf : (Fintype.card (Site f):ℝ)≤W)
variable (D : ℝ) (hc : Golf (Lapis.table F k T.up T.high) (Lapis.mist F O T.up) (Lapis.orbit F ρ) (Lapis.gram F T.up T.high ρ k) n D u v p) (hr : u ≤ (A.tables T.high S.patch).horizon) {x:Positions (Uniform.Primary c G)} (hx : ‖x‖ < u) (hb : 0<β)
variable (δ : ℝ) (hh : 0 <δ) (hδ : B.threshold ≤ δ)
    (H : ∀ i:S.Choices, ∀ U:F.Slice G, Alive S (F.drape U) i → (∀ j: Pressure.Cell f,toll (F.drape U) j ≤ δ) → (∀ b, wire (S.prediction (F.drape U) i) (represent (tint G _ x)) b ≤ δ) →
      ∃ z : Poll.Body (Precision.Key F G), ‖weld (Precision.Key F G) z‖ ≤ (A.tables T.high S.patch).safety ∧ U=draw F (represent (tint G _ x)) z) (hW : β*meterQ (A.tables T.high S.patch) n W*‖x‖ + (A.tables T.high S.patch).gap/4*D^2 ≤ β*(S.kernel.penalty*δ^2/2))
include he ha h hv hV hf hc hr hx hb hh hδ H hW
lemma polar (i:S.Choices) (U:F.Slice G) (heU : flags B.threshold (F.drape U) = ∅) (hs : Alive S (F.drape U) i)
    (ho : U∉ staying F (g x) (G₀) D (V x)) : let Q:= mainTerm T.high T.up (F.drape U)+noiseTaylor S (V x) (F.drape U) i;
      -β*Q-Precision.loop T.up (F.drape U) ≤
        -(R).gap/4*D^2+W*PathData.loopsPrice B β C Λ +p+tapir (R) W -coverLog F T O k ρ β x:= by
  intro Q; let Δ:= (R).gap/4*D^2; let L:=PathData.loopsPrice B β C Λ
  have hl : 0 ≤ Λ:=(tsum_nonneg h.two.1).trans h.two.2.2; have hsC : 0 ≤ C:= ((tsum_nonneg h.three.1).trans h.three.2.2)
  have ht:=B.threshold_pos; have hL : 0 ≤ L:=by unfold L PathData.loopsPrice; positivity
  have hX:=abs_le.mp (colo F T k A ρ O he ha h W hV hc hr _ hx β)|>.2
  have hh' := mul_le_mul_of_nonneg_right hf hL
  let u':= F.drape U
  by_cases H₀:∀ b, wire (S.prediction u' i) (V x) b ≤ δ
  · have hz := loopbill T.up B u' h heU
    have hp': Λ* B.threshold^2 ≤ L:= le_add_of_nonneg_left (by positivity)
    have hp := (abs_le.mp (hz.trans ((mul_le_mul_of_nonneg_left hp' (Nat.cast_nonneg _)).trans hh'))).1
    obtain ⟨z,hz,ht'⟩:= H i U hs (fun j=> (Pane.lucid B u' heU j).trans hδ) H₀
    have hzs : combineH (G:=G) F (x,z)∈ closedBall 0 (R).safety := by
      change meetVar x (weld K z)∈ _; rw [mem_closedBall_zero_iff,norm_meet]; exact max_le (((hx.le.trans hr).trans he.2.1).trans he.2.2.2.1) hz -- order checks
    have hQ: Q=φ (x,z):= by
      unfold Q; rw [ht']; change Lapis.table F i T.up T.high (x,z)=φ _; obtain ⟨hu,hT⟩:= A.receipt F k h ha rfl rfl; exact hT _ (closedBall_subset_ball hu.reserveH_lt hzs) i
    have hS := gS β hb
    have hD : D*(G₀) ≤ ‖z-g x‖ := by
      rw [mul_comm]; contrapose! ho; rw [ht']; refine ⟨z,⟨(G₀)⁻¹ • (z-g x),mem_closedBall_zero_iff.mpr ?_,?_⟩,rfl⟩
      · rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hS.1).le]; exact (inv_mul_le_iff₀ hS.1).mpr ho.le
      dsimp only; rw [smul_inv_smul₀ hS.1.ne',add_sub_cancel]
    have hi:= mul_le_mul_of_nonneg_right (climbs F T k A ρ he ha h x (hx.trans_le hr) (G₀) D hS.1 hc.off z hzs hD) hb.le
    rw [mul_assoc _ _ β,hS.2,mul_one, ← hQ] at hi; linarith only [hi,hp,hX]
  have hu := T.up.whole T.high B β hb.le u' h; rw [Pane.crystalline T.up T.high B β u' heU] at hu
  have hg:= crashed i hh.le H₀; have hF:= mul_le_mul_of_nonneg_left ((le_abs_self _).trans (costQ F T k A ρ he ha h W hv hV x (hx.trans_le hr))) hb.le; unfold Q
  change S.kernel.penalty * δ ^ 2 / 2 ≤ noiseTaylor S (V x) (F.drape U) i at hg
  linarith only [hu,hh',hW,mul_le_mul_of_nonneg_left hg hb.le,hF,hX]

omit he ha h hv hV hf hc hr hx hb hh hδ H hW in
lemma rays (U:F.Slice G) (x:X) : 0 ≤ overall F T B β (V x) U := by
  apply sum_nonneg; intro i _; unfold actU taggedKernel; rw [Pane.sparkling, true_point]
  have he : 0 < π':= pow_pos (inv_pos.mpr (S.penaltyZ_pos _)) _; have h:= S.likelihood_pos (F.drape U) i
  split <;> positivity

lemma overest (U:F.Slice G) (heU : U∉ staying F (g x) (G₀) D (V x)) :
    overall F T B β (V x) U ≤ (π')*Real.exp (-(R).gap/4*D^2+W*PathData.loopsPrice B β C Λ+p+tapir (R) W-coverLog F T O k ρ β x) := by
  let Kx:=-(R).gap/4*D^2+W*PathData.loopsPrice B β C Λ+p+tapir (R) W-coverLog F T O k ρ β x
  let w:=F.drape U
  have hp : 0<π':= pow_pos (inv_pos.mpr (S.penaltyZ_pos _)) _
  have hl (i:S.Choices): actU F T i B β (V x) U ≤ (π')* S.likelihood w i* Real.exp Kx:= by
    have ht:= S.likelihood_pos w i
    by_cases hi: Alive S w i
    · by_cases heU': flags B.threshold w=∅
      · rw [acts F T i B β _ _ heU']; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (polar F T k A ρ O B β he ha h W hv hV hf D hc hr hx hb δ hh hδ H hW i U heU' hi heU)) (mul_nonneg hp.le ht)
      unfold actU; rw [Pane.sparkling,if_neg heU',mul_zero]; positivity
    unfold actU taggedKernel; rw [dead hi]; simp
  exact (sum_le_sum fun i _=> hl i).trans_eq (by rw [← sum_mul,← mul_sum,S.chosen ha.1,mul_one])
end YM.PhysicalNext.Repeat.Fare
