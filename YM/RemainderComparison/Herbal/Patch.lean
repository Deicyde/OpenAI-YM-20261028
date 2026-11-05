import YM.RemainderComparison.Herbal.Chart
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Herbal
open Function Filter Metric Set Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext.Repeat Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.Scheduling ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Sienna Fare Germ Token
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {r j n k m : ℕ}
variable {c f : Side} {S : StepData c f}
variable {E Y : Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {Z σ C D W A:ℝ} {s:Set E}{ι : Type}
structure Colony (P : Config G f →ℝ) (j k:ℕ)(Z A:ℝ) : Prop where
   tall (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E]
      (U:E→ Config G f) (h: Inputs U k Z) : ∀ y:E,‖y‖<1 → Brush k A 1 (P ∘ U) y
   mode (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E]
      (U:E→ Config G f) (h: Inputs U k Z) : Bud k j (P ∘ U) 0
/-- Authenticates supplies for GROUP actual estimates on sunny neighborhoods.
 `t`: admit physical f (c for AUX formal projection) mesh threshold.
 Uses full group/wearing.R visibility. Support distance costs bought BEFORE.
 Here A coefficient growth *does* permit physical poly costs in volume on AUX.
 Only sold on authorized virtual torus; don't transfer these estimates on physical denotations!
-/
structure Sect (P:Config G f →ℝ)(t:ℝ)(j k:ℕ)(Z A:ℝ) : Prop extends Colony P j k Z A where
   vigor : GaugeInvariant P
   localM : Measurable P
   value : ∀ U, flags t U=∅ → ‖P U‖≤A*t^j
variable (X:ι→Atom G j)(q:ι→ Site f)(a:ι→ℝ)(p:ι→ Signed)
    (hσ:0<σ)(hX:SumBudget (fun i=> |a i| * (X i).budget σ) C)

def club (U:Config G f):= ∑' i,a i * (X i).unmasked (pull (p i) 0 U) (q i)
include hσ hX
omit hσ in
lemma campus_nn : 0≤C:= (tsum_nonneg hX.1).trans hX.2.2 -- other lemma?
lemma aColony (hn : 0≤Z) : Colony (club X q a p) j k Z (C*prize k j G σ Z):= by
  let A:=prize k j G σ Z; let c i:=|a i| * (X i).budget σ * A
  let f' i (U:Config G f):=a i * (X i).unmasked (pull (p i) 0 U) (q i)
  have hc:SumBudget c (C*A):= ⟨fun i=> mul_nonneg (hX.1 _) (prizes_pos hn hσ),hX.2.1.mul_right A,by unfold c; rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hX.2.2 (prizes_pos hn hσ)⟩
  have hp (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E] (U:E→ Config G f) (h:Inputs U k Z) (i) (y:E)(hy:y∈ball 0 1): Allows k (fun z=>f' i (U z)) y (c i):= by
    unfold c; rw [mul_assoc]; exact (currency h _ _ _ hσ y (mem_ball_zero_iff.mp hy).le).smul (a i)
  have hS (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E] (U:E→ Config G f) (h:Inputs U k Z) (x) (hx:‖x‖<1): Brush k (C*A) 1 ((club X q a p) ∘ U) x:= dons isOpen_ball (convex_ball _ _).isPreconnected hc (hp E U h) _ (mem_ball_zero_iff.mpr hx)
  refine ⟨hS, fun E _ _ U h=> ⟨(hS E U h 0 (by simp)).smooth,fun i hi hi'=>?_⟩ ⟩
  unfold normJ; apply norm_eq_zero.mpr; unfold club; simp only [comp_def]
  rw [iterated_at_sum isOpen_ball (convex_ball _ _).isPreconnected hc.2.1 (hp E U h) (mem_ball_self zero_lt_one) i hi]; refine (tsum_congr ?_).trans tsum_zero
  intro m
  unfold f'
  simp_rw [← smul_eq_mul]; have hh:=Beds.prestige h (X m) (q m) (p m)
  rw [iteratedFDeriv_const_smul_apply' (hh.1.of_le (by exact_mod_cast hi)),norm_eq_zero.mp (hh.2 i hi hi'),smul_zero]

lemma tour (V:Config G f)(b : BudgetPoint)(hv:flags b.threshold V=∅) : ‖club X q a p V‖≤ C*b.threshold^j:=by
   let y:=b.threshold^j; have hp : 0≤y:= pow_nonneg b.threshold_pos.le _
   have ht i : ‖a i * (X i).unmasked (pull (p i) 0 V) (q i)‖≤ |a i| *(X i).budget σ*y:= by
     let U:=pull (p i) 0 V; have he : flags b.threshold U=∅:=Finset.image_eq_empty.mp ((Work.H03.flags_send (p i) 0 b.threshold V).trans hv)
     have hY : Healthy b.threshold ((X i).footprint (q i)) U:=by unfold Healthy; rw [he]; exact Finset.disjoint_empty_right _
     rw [norm_mul,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
     have hh:= RG.healthy_atom (X i) b U (q i)
     rw [Atom.placed,masked_eq _ _ _ _ hY] at hh
     exact hh.trans (mul_le_mul_of_nonneg_right ((X i).lower_budget _ hσ) hp)
   have he:= hX.2.1.mul_right y; have hy:= he.of_nonneg_of_le (fun _=>norm_nonneg _) ht; unfold club
   refine (norm_tsum_le_tsum_norm hy).trans ((hy.tsum_le_tsum ht he).trans ?_)
   rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hX.2.2 hp

lemma aSect [Countable ι](b: BudgetPoint)(hz:0≤Z)(hh:∀ i,(X i).Invariant) :
    Sect (club X q a p) b.threshold j k Z (C*(1+prize k j G σ Z)) := by
   have hp : 0≤C:=campus_nn X a hX
   let H:= aColony X q a p hσ hX (k:=k) hz; have he:C≤C*(1+prize k j G σ Z):= le_mul_of_one_le_right hp (le_add_of_nonneg_right (prizes_pos hz hσ))
   refine ⟨⟨fun E _ _ U h y hy=>(H.tall E U h y hy).climb (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hp) le_rfl,H.mode⟩,fun g U=>?_ ,?_,fun U hu=>(tour X q a p hσ hX U b hu).trans (mul_le_mul_of_nonneg_right he (pow_nonneg b.threshold_pos.le _))⟩
   · exact tsum_congr fun i=>by unfold Atom.unmasked; simp only [Work.F05.pull_gauge_zero, Work.F05.slot_gauge]; exact congr_arg (a i * ·) (hh i ..)
   unfold club; apply Measurable.tsum
   intro i; apply measurable_const.mul; apply ((X i).unmasked_cont _).measurable.comp; fun_prop
-- upper estimate monotonic only in A
omit hX hσ
lemma climbed {P:Config G f→ℝ} (hP:Sect P W j k Z D)(hW:0≤W)(hC:D≤C):Sect P W j k Z C:= ⟨⟨fun E _ _ U h y hy=>(hP.tall E U h y hy).climb hC le_rfl,hP.mode⟩,
        hP.vigor,hP.localM,fun U hu=>(hP.value U hu).trans (mul_le_mul_of_nonneg_right hC (pow_nonneg hW _))⟩
end YM.RemainderComparison.Herbal
