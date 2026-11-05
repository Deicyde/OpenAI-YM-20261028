import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Annulus
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Shutter
import YM.Next.SCHEDULE.GridCost

/-!
# Γ charts and masks

Insert on intact data; guards on real a. Larger patches allow optional
Mayer letters when gamma off. Uses both ends/symmetry neighborhoods.
Meas/costs incl log J (not assuming ≤1 globally). Signs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable (X : Coat T F)

/-- For Hot sites only. Hard Y not here. -/
def cone (a : ℝ) (u : Directions G f) (i : Bond f) := X.χ.innerShare (a*X.t) ‖u i‖

def plaza (O : Support c) := univ.filter fun i : Bond f => X.Hot i ∧ ¬Disjoint O (ends S i)
def booth (X : Coat T F) (i : Site c) := X.plaza (Animals.neighbors X.B i)
def enforce (a : ℝ) (U : Directions G f) (Y : Finset (Bond f)) := ∏ i∈Y,X.cone a U i

def gentry (Ñ : ChartRatio G) (a : ℝ) (U : Directions G f) (i : Bond f) := X.cone (2*a) U i * Real.log (Ñ.J (U i))

lemma booked (a : ℝ) (U : Directions G f) (i : Bond f) : X.cone a U i ∈ Set.Icc 0 1 := X.χ.range _
lemma ages (i : Bond f) (o : Site c) (h : X.Hot i) (hp : distAt S i o ≤ X.B) : i∈ X.booth o :=
    mem_filter.mpr ⟨mem_univ _,h, not_disjoint_iff.mpr ⟨_,(Animals.neighbors_mem ..).mpr hp, center_end i⟩⟩
lemma conserve (Y : Finset (Bond f)) (a : ℝ) (U : Directions G f) : X.enforce a U Y ∈ Set.Icc 0 1 :=
    ⟨Finset.prod_nonneg fun i _ => (booked X a U i).1, prod_le_one (fun i _ => (booked X a U i).1)
      (fun i _ => (booked X a U i).2)⟩
lemma premiere {a : ℝ} (hp : 0<a*X.t) (U : Directions G f) (i : Bond f) (h : ‖U i‖ ≤ a*X.t) :
    X.cone a U i=1 := by
  rw [cone, Chi.innerShare]; apply X.χ.to_one
  have ht : ‖U i‖/(a*X.t) ≤ 1 := (div_le_one hp).2 h
  have hs : 0 ≤ ‖U i‖/(a*X.t) := by positivity
  nlinarith
lemma amount {a : ℝ} (ha : 0<a*X.t) (U : Directions G f) (i : Bond f) (h : X.cone a U i≠0) :
    ‖U i‖ ≤ 2*a*X.t := by rw [mul_assoc]; exact (X.χ.chosen_lt _ _ ha h).le
lemma serves {a : ℝ} (ha : 0<a*X.t) (U : Directions G f) (i : Bond f) (hi : X.cone a U i ≠ 0) :
    X.cone (2*a) U i=1 := X.premiere (by rw [mul_assoc]; positivity) _ _ (amount X ha U i hi)
lemma doorway {a : ℝ} (ha : 0<a*X.t) (U : Directions G f) (i : Bond f) (h : X.cone a U i≠0) {Ñ : ChartRatio G}
    (hF : LocalRatio Ñ) (hp : 2*a*X.t < Ñ.radius) :
    (U i) ∈ Metric.ball (0:G.Color) Ñ.radius ∧ Real.exp (X.gentry Ñ a U i)=Ñ.J (U i) := by
  have he := Metric.mem_ball.mpr (show dist (U i) 0 < Ñ.radius by rw [dist_zero_right]; exact (amount X ha U i h).trans_lt hp)
  refine ⟨he,?_⟩
  rw [gentry,X.serves ha U i h,one_mul, Real.exp_log (hF.pos (U i) he)]

lemma covering {a : ℝ} (ha : 0<a*X.t) (Y : Finset (Bond f)) (U : Directions G f)
    (h : ∀ i∈Y,X.cone a U i≠0) : X.enforce (2*a) U Y=1 := Finset.prod_eq_one (fun i hi => X.serves ha U i (h i hi))
lemma protection (O : Support c) {a : ℝ} (ha : 0<a*X.t) (U : Directions G f) (h : X.enforce a U (X.plaza O)≠0) :
    ∀ i : Bond f, i∈X.plaza O → ‖U i‖ ≤ 2*a*X.t := fun i hi => X.amount ha U i fun he => h <| prod_eq_zero hi he
lemma protection_pack {a : ℝ} (ha : 0<a*X.t) (A : Stores S) (d : ℕ) (U : Directions G f)
    (h : X.enforce a U (X.plaza (A.dome d))≠0) : X.Controlled d A U (2*a*X.t) := fun i hi hg =>
  X.protection _ ha U h i (mem_filter.mpr ⟨mem_univ _,hg, Finset.not_disjoint_iff.mpr ⟨_,hi,center_end _⟩⟩)

/-- Broad gamma can accompany the full chart substitution. -/
lemma buys_empty (X : Coat T F) {a γ W : ℝ} (hF : ShellAccess S G X.x W X.width γ)
    (hm : γ*X.width ≤ a) {Ñ : ChartRatio G} (_h : LocalRatio Ñ) (hy : a*X.t < Ñ.radius)
    (U : Config G f) (hp : Seeded X.seeds U X.k X.V X.x W) (hf : Alive S U X.k)
    (hs : SliceSet S F U) :
    ∀ i : Bond f, X.Hot i → ∃ v ∈ Metric.ball (0:G.Color) Ñ.radius, ‖v‖ ≤ a*X.t ∧
      U i=G.lieExp v*replica S.ratio X.V i := by
  intro i he
  let z := U i*(replica S.ratio X.V i)⁻¹
  have hd : Interior S X.x W (atEdge S i) (X.B/4) U X.k X.V := Interior.of_actual U X.V X.k (atEdge S i) hp hf
    fun h => active_far X.seeds i he (Corona.halo_mono (by omega) (Finset.Subset.refl _) h)
  have hc : G.chord z ≤ X.width*X.t := hF.exacts F U X.V i X.k hs hd
  have hv := hF.log
  have hz : G.chord z ≤ 2*(X.width*X.t) := hc.trans (by linarith [hv.down])
  let v := G.plog (G.mat z)
  have hh : ‖v‖ ≤ a*X.t := calc
    _ ≤ γ*G.chord z := hv.cap _ hz
    _ ≤ γ*X.width*X.t := by rw [mul_assoc]; gcongr; exact hv.price.le
    _ ≤ _ := mul_le_mul_of_nonneg_right hm (temp_nonneg _)
  exact ⟨v,Metric.mem_ball.mpr (by rw [dist_zero_right]; exact hh.trans_lt hy),hh,by rw [show G.lieExp v=_ from hv.right z hz]; unfold z; group⟩

/-- at all (even chart-outside) arguments. -/
theorem germ_charge {Ñ : ChartRatio G} (h : LocalRatio Ñ) (L : Side) {a : ℝ} (ha : 0<a) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S)
      (F : Forest S.ratio) (X : Coat T F), X.x=x → S.patch.L=L →
      0<X.t → 4*a*X.t < Ñ.radius ∧ ∀ i U, |X.gentry Ñ a U i| ≤ C*X.t := by
  let f (v : G.Color) := Real.log (Ñ.J v)
  have hh : AnalyticAt ℝ f 0 := (((h.germ 0 (Metric.mem_ball_self h.patch)).log (by rw [h.anchored]; norm_num))).analyticAt
  obtain ⟨C,r,hC,hr,H⟩ := Next.Fluctuations.chart_linear_cost _ _ hh
  refine ⟨C*(4*a),by positivity,?_⟩
  filter_upwards [((Rate.flame (G:=G) (L:=L)).mul_left (4*a)).below (by norm_num) _
    (lt_min hr (half_pos h.patch))] with x hx c n S T F X hX hL hr'
  have he : 4*a*X.t ≤ min r (Ñ.radius/2) := by unfold Coat.t; rw [hX,hL]; exact (le_abs_self _).trans hx
  obtain ⟨hg,hy⟩ := le_min_iff.mp he
  refine ⟨lt_of_le_of_lt hy (by linarith [h.patch]),fun i U => ?_⟩
  rw [gentry,abs_mul]
  by_cases hk : X.cone (2*a) U i=0
  · rw [hk,abs_zero,zero_mul]; positivity
  have ht : ‖U i‖ ≤ 4*a*X.t := (X.amount (show 0 < 2*a*X.t by positivity) U i hk).trans_eq (by ring)
  have hb := H (U i) (show ‖U i-0‖ ≤ r by rw [sub_zero]; exact ht.trans hg)
  simp only [sub_zero,f,h.anchored,Real.log_one] at hb
  rw [abs_of_nonneg (X.booked (2*a) U i).1]
  apply (mul_le_of_le_one_left (abs_nonneg _) (X.booked (2*a) U i).2).trans
  exact (hb.trans (mul_le_mul_of_nonneg_left ht hC.le)).trans_eq (by ring)
end YM.ConnectedActivityE6.Coat
