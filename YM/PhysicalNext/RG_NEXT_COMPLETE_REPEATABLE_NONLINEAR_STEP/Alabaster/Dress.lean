import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Indigo
/-!
# Compose real Clutch over changing β and warp rays. First census
 at OLD R; cost ∆input prices includes E values only at *uniform* physical reads. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical Interval
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {Pt : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G Pt} {o : Target.Order G W} {R I : RG.Rep G f} {P : Facing R I}
    {p μ C v M d r D K' : ℝ} {i : ℕ} {χ : Chi} {H : Cash W p μ L Q o C T R}
variable (X : Coat T F) (Ξ : Utopia H i v d r D χ)
section cloth
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (z : Air f G) (U:E→ Config G c) (V:E→ Directions G f) (Z:E → Air f G) (y:E)
    (hx:X.width=o.K) (hv:X.x=p) (hχ:X.χ=χ) (hm:X.manifest) (h: Mode U y i v)
    (hp: Clutch X z o.a R.beta d y i U V Z)
def wraps (T : Tube G S) (X : Coat T F) (β : ℝ) (a W : ℝ) (Ñ : ChartRatio G) (b : ℝ) (l : ℕ) (R : RG.Rep G f) (k : Finset ℕ) (z : Air f G) (U:E→ Config G c) (V:E→Directions G f) (Z:E→Air f G) (i: Head S) (p:E) :=
    Polar.ember (vary X (U p)) a R W Ñ (V p) (X.input (worldZ X β z)) (b • Z p) k l i
local notation "J" => wraps T X R.beta o.a W Q.table 1 Q.halo R
include hx hv hχ hm hp h
lemma sung (k : Finset ℕ) (s : Head S) (hy : Healthy (Pressure.temp X.x) (H.supportP s) X.V) :
    Brush i (coin Ξ s) 1 (J k z U V Z s) y:= by
  have h' := Ξ.stream E F X U V Z y z hv hx hχ hm h hp k s hy
  have hB : X.B=radiusB p:=hv ▸ rfl
  unfold coin Silica.Utopia.tag; rw [← hB] -- changes other uses p
  exact h'.trim.shimmy (Eventually.of_forall fun x=>by unfold wraps; rw [one_smul])
local notation "f₁" => (fun u s=> Polar.logMoment (vary X (U u)) o.a R Q.table (V u) (X.input (worldZ X R.beta z)) (Z u) s)
omit [FiniteDimensional ℝ E] hχ h in
lemma lovely (s:LogIndex c f) (ht : Healthy (Pressure.temp X.x) (H.supportP (.inr (.inr (.inl s)))) X.V) :
    |(f₁) y s| ≤ H.opt (.inr (.inl s)):= by
  let B:= X.liftA R.beta z; let l:=H.laws
  obtain ⟨Y₁,Y₂,-⟩:= H.quotes F X hv hx hm; have hP := l.data.room; have hK:=l.intake
  have hh : Room Pt S T X.x:=hv ▸ hP
  have he : (f₁) y s=X.farLog R o.a Q.table z s:= by
    have hy:=Clutch.base0 hp hh hm; change Polar.logMoment _ _ _ _ _ _ _ _=_; rw [hp.tipped,hp.birth,hy,← Vine.shine X hh hm]
    have hv' := Polar.leisure X o.a R Q.table hh hm Q.buys z B rfl s (show Healthy (Pressure.temp X.x) (roadway T R X.B Q.halo s) X.V from ?_)
    · unfold raiseAir at hv'; apply Real.exp_injective; exact (sub_left_inj.mp hv').symm -- which
    rw [show X.B=radiusB p from congr_arg _ hv]; exact ht
  rw [he]; exact (Y₂ s z).1
end cloth
variable {K A' : ℝ}
-- uniform gates. ON Clutches no detour. price from Mask primitive with same χ, temps.
lemma lint (S : StepData c f) (χ: Chi) (q a : ℝ) (_ha:0<a*Pressure.fiery G q S.patch.L) (i:ℕ) (d:ℝ):
    ∃ b : ℝ, 1≤b ∧ ∀ {T: Tube G S} (F: Forest S.ratio) (X : Coat T F), X.χ=χ→X.x=q→ ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (β:ℝ) (z:Air f G) (U:E→ Config G c) (V:E → Directions G f) (Z:E→Air f G) (x:E), Clutch X z a β d x i U V Z → ∀ I : Finset (Bond f), Brush i b 1 (fun y=>X.enforce (2*a) (V y) I) x:= by
  let t:= 2*a*Pressure.fiery G q S.patch.L
  let A v:= χ.innerShare t ‖(v:G.Color)‖
  obtain ⟨C,hC,H⟩:= Brush.compact (k:=i) (s:=closedBall 0 (2*t)) (f:=A) (isCompact_closedBall ..) (fun e _=> (show ContDiff ℝ (↑i : WithTop ℕ∞) A from (by unfold A Chi.innerShare; simp_rw [div_pow]; exact (χ.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).comp ((contDiff_norm_sq ℝ).div_const _))).contDiffAt)
  let g:= 1+ |Lantern.clump i (d+2*t) C|; have hg:1 ≤ g:= le_add_of_nonneg_right (abs_nonneg _)
  let m:=Fintype.card (Bond f)
  refine ⟨g^m*(1+(m:ℝ))^i,one_le_mul_of_one_le_of_one_le (one_le_pow₀ hg) (one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))),?_⟩
  intro T F X hχ hx E _ _ β z U V Z x h I
  have hh j : Brush i g 1 (fun v=> X.cone (2*a) (V v) j) x:= by
    by_cases he:(fun v=> X.cone (2*a) (V v) j)=ᶠ[𝓝 x] fun _=>0
    · exact Brush.zi he (zero_le_one.trans hg) zero_le_one
    obtain ⟨hc,hp⟩:= Clutch.fostered h j (b:=2*a) (by rw [mul_assoc]; exact mul_pos (by norm_num) h.pulse) he
    have hl : X.t=Pressure.fiery G q S.patch.L:= by unfold Coat.t; rw [hx]
    have hy : (2*(2*a)*X.t)=2*t:= by rw [hl]; unfold t; ring
    rw [hy] at hc hp; apply ((Lantern.composite hp (H _ (mem_closedBall_zero_iff.mpr hc))).climb ((le_abs_self _).trans (le_add_of_nonneg_left zero_le_one)) le_rfl).shimmy; exact Eventually.of_forall fun i=>by unfold cone; rw [hχ,hl]; rfl
  have hp:= Brush.trim (Brush.all_prod I _ (fun _=>g) (fun _=> 1) (fun i _=> hh i)); simp only [sum_const,nsmul_eq_mul,mul_one, prod_const] at hp; apply hp.climb _ le_rfl; unfold m; gcongr <;> exact Finset.card_le_univ _
end YM.PhysicalNext.Repeat.Alabaster
