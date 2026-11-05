import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Fare.Bingo
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lapis.Quarry
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Fare
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio) (T : Tube G S) (k : S.Choices)
    {u v D s m l p σ C Λ : ℝ} {n : ℕ}
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "K" => Precision.Key F G
local notation "Y" => Poll.Body K
variable (A : Push.Uniform.Before G σ C S.patch.J S.kernel (n+3)) (ρ : Bid.Dir G c→ AxisChart G F)
    (he : A.Service F T.high T.up ρ) (ha : Larger (G:=G) S) (h : T.up.Bounds T.high σ C Λ) {xX b : ℝ}
    (hu : u ≤ (A.tables T.high S.patch).horizon)
local notation "R" => A.tables T.high S.patch
local notation "C₀" => Before.Service.trailCost (R) (n+3)
local notation "r" => Lapis.orbit F ρ
local notation "V" => (fun x:Xs=>represent (tint G _ x))
local notation "M" => combineH (G:=G) F
local notation "P" => Positions (Joint F G)
include he ha h hu k
lemma fury (hb : 0 < b) (x:Xs) (hx: ‖x‖<u) (z:Y) (hz: ‖z‖ ≤ D) :
    ‖weld K (r x+b • z)‖ ≤ C₀*u+b*D ∧ ‖M (x,r x+b • z)‖ ≤ (1+C₀)*u+b*D := by
  have hsD:0 ≤ D:=(norm_nonneg _).trans hz; have hs:=evacuated F T.up k ρ A ha h he _ (hx.trans_le hu)
  have hc:0<C₀:= (he.trail_lipschitz h ha rfl rfl).1
  have h₁ : ‖weld K (r x+b • z)‖ ≤ C₀*u+b*D:= by
    rw [map_add,map_smul]; apply (norm_add_le ..).trans (add_le_add (hs.trans (mul_le_mul_of_nonneg_left hx.le hc.le)) ?_)
    rw [norm_smul,Real.norm_of_nonneg hb.le]; apply mul_le_mul_of_nonneg_left _ hb.le; exact ((weld K).toContinuousLinearMap.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) (Lapis.climb K)).trans hz)
  have Hu:0<u:=(norm_nonneg _).trans_lt hx
  refine ⟨h₁,?_⟩; change ‖meetVar x (weld K (r x+b•z))‖≤_; rw [norm_meet]; apply max_le <;> linarith [mul_pos Hu hc,mul_nonneg hb.le hsD]
variable (B : BudgetPoint) (β : ℝ)
local notation "G₀" => gStep β
lemma slack {x:Xs} (hx: ‖x‖<u) (hβ:0<β) (hc:(1+C₀)*u+G₀*D≤1)
    (Hr : ∃ y:F.Slice G,y∈staying F (r x) (G₀) D (V x)∧∀ i: Pressure.Cell f,toll (F.drape y) i ≤ B.threshold/2)
    (hp : 0<l) (ht:∀ i:P,∀ j:P,∀ x: Cell f, ‖i‖≤1 → ‖j‖≤1 → |toll (Uniform.fine G F i) x - toll (Uniform.fine G F j) x| ≤ l*‖i-j‖)
    (hd : l*((1+C₀)*m+G₀*(D+D)) ≤ B.threshold/2) : ∀ y:Xs, ‖y‖<u → ‖y-x‖ ≤ m → ∀ z:Y, ‖z‖≤D → flags B.threshold (F.drape (draw F (V y) (r y+G₀ • z)))=∅ := by
  obtain ⟨w,⟨d,⟨z₀,hz₀,rfl⟩,rfl⟩,HM⟩:=Hr
  intro y hy HY z hz
  let e : ℝ:= G₀
  have hz₀:=mem_closedBall_zero_iff.mp hz₀
  have hb:0<e:=(gS β hβ).1
  let Y₀ := r x + e • z₀; let Y' := r y + e • z
  have hD := ht (M (y,Y')) (M (x,Y₀))
  have hyy : ‖M (y,Y')‖≤1:= (fury F T k A ρ he ha h hu hb _ hy z hz).2.trans hc
  have hzz : ‖M (x,Y₀)‖≤1:= (fury F T k A ρ he ha h hu hb _ hx z₀ hz₀).2.trans hc
  let t':=(1+C₀)*m+e*(D+D); let L:=weld K
  obtain ⟨hC,hH⟩:=he.trail_lipschitz h ha rfl rfl
  have hh: ‖L Y'- L Y₀‖ ≤ C₀*m+e*(D+D) := by
    have hc : ‖L (r y)-L (r x)‖ ≤ C₀*m:= (hH _ (mem_ball_zero_iff.mpr (hy.trans_le hu)) _ (mem_ball_zero_iff.mpr (hx.trans_le hu))).trans (mul_le_mul_of_nonneg_left HY hC.le)
    have ht: ‖L (z-z₀)‖≤D+D:= (L.toContinuousLinearMap.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) (Lapis.climb K)).trans ((norm_sub_le ..).trans (add_le_add hz hz₀)))
    have hp:Y'-Y₀ = (r y-r x)+ e • (z-z₀):= by unfold Y' Y₀; rw [smul_sub]; abel
    rw [← map_sub,hp,map_add,map_smul,map_sub L (r y)]; apply (norm_add_le ..).trans (add_le_add hc ?_); rw [norm_smul,Real.norm_of_nonneg hb.le]; exact mul_le_mul_of_nonneg_left ht hb.le
  have he: ‖M (y,Y')-M (x,Y₀)‖ ≤ t':= by
    have hm: 0 ≤ m := (norm_nonneg _).trans HY; have hs:0≤D:=(norm_nonneg _).trans hz
    rw [← map_sub]; change ‖meetVar (y-x) (L (Y'-Y₀))‖ ≤ _; rw [norm_meet, map_sub]; apply max_le
    · unfold t'; have h':0≤ e*(D+D):=by positivity
      exact HY.trans ((le_mul_of_one_le_left hm (le_add_of_nonneg_right hC.le)).trans (le_add_of_nonneg_right h'))
    exact hh.trans (by unfold t'; rw [add_mul,one_mul]; linarith)
  apply Finset.eq_empty_of_forall_notMem; intro i hh; obtain ⟨p,-,hv⟩:= (flags_spec ..).mp hh
  have hi:= ((hD p hyy hzz).trans ((mul_le_mul_of_nonneg_left he hp.le).trans hd))
  apply hv.not_ge
  change toll (Uniform.fine G F (M (y,Y'))) p ≤ B.threshold
  have hu:toll (Uniform.fine G F (M (x,Y₀))) p ≤ B.threshold/2:= HM p
  linarith only [hu,(abs_le.mp hi).2]

lemma gamma (hb : 0<b) {x:Xs} (hx:‖x‖<u) (hc:(1+C₀)*u+b*D < (R).initial) : ∀ z:Y, ‖z‖≤ D → ∀ l:S.Choices, Lapis.table F l T.up T.high (x,r x+b • z)=Lapis.table F k T.up T.high (x,r x+b•z) := fun z hz l=>
    (A.receipt F k h ha rfl rfl).2 (M (x,r x+b•z)) (mem_ball_zero_iff.mpr ((fury F T k A ρ he ha h hu hb _ hx z hz).2.trans_lt hc)) l
lemma mouthF (O : ChartRatio G) (heO : Uniform.shade G*(C₀*u+b*D)<O.radius) (hb : 0<b) {x:Xs} (hx:‖x‖<u) : ∀ z:Y, ‖z‖≤ D → windmill F (r x+b • z)∈mouth O := fun z hz i _=>
    mem_ball_zero_iff.mpr ((carries F i _).trans_lt ((mul_le_mul_of_nonneg_left (fury F T k A ρ he ha h hu hb _ hx z hz).1 (Uniform.shade_pos _).le).trans_lt heO))
end YM.PhysicalNext.Repeat.Fare
