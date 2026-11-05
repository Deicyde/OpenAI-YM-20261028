import YM.Pert.Align.Recoil
import YM.Pert.Lattice.Symbol
/-! Self subtraction uses the same linear chart on the infinite cover *independently* of the orbital potential measure. -/
noncomputable section
set_option autoImplicit false
namespace YM.Pert.Align
open Full Orb Maxwell MeasureTheory Set Lattice Function
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {u : ℝ}
variable {j k : ℕ}
open Atom

def shoot (c : Channel G) (q : E4) (v : G.ColorIndex) (x : Cover) (f : Axis) : ℝ := if c.color = v ∧ c.axis=f then Full.wave c.sine x q else 0
def locals (G : Gauge) := Bool × (Axis × G.ColorIndex)
def split (G : Gauge) : Channel G ≃ Bool × (Axis × G.ColorIndex) where
  toFun c := (c.sine,c.axis,c.color)
  invFun p := ⟨p.1,p.2.1,p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
lemma shoot_dual (c : Channel G) (q v x f) : inner ℝ (unitColor G v) (material c q (x,f)) = shoot c q v x f := by
  unfold material shoot; split_ifs with h₁ h₂ h₂
  · rw [real_inner_smul_right,real_inner_comm, to_color,EuclideanSpace.basisFun_apply,PiLp.single_apply,one_mul, if_pos h₂.1.symm,mul_one]
  · have he := fun hv: c.color=v=> h₂ ⟨hv,h₁⟩
    rw [real_inner_smul_right,real_inner_comm,to_color,EuclideanSpace.basisFun_apply,PiLp.single_apply,one_mul,if_neg (Ne.symm he),mul_zero]
  · exact False.elim (h₁ h₂.2)
  · simp only [zero_mul,zero_smul,inner_zero_right]
lemma channel_fusion (q : E4) (u v : G.ColorIndex) (x y : Cover) (i j : Axis) : (∑ c:Channel G, shoot c q u x i * shoot c q v y j) = (if j=i then 1 else 0) * inner ℝ (unitColor G u) (unitColor G v) * Full.wave false (x-y) q := by
  classical
  rw [to_color,unitPaint]
  classical
  by_cases h : j=i∧v=u
  · have hj:=h.1; have hu:=h.2; subst i; subst v; rw [← Equiv.sum_comp (split G).symm]; unfold split shoot; dsimp; simp_rw [Fintype.sum_prod_type]
    have he (b) (i : Axis): (∑ h : G.ColorIndex, (if h=u∧i=j then Full.wave b x q else 0) * (if h=u∧i=j then Full.wave b y q else 0)) = if i=j then Full.wave b x q * Full.wave b y q else 0 := by
      by_cases hi : i=j
      · rw [if_pos hi, Finset.sum_eq_single_of_mem u (Finset.mem_univ _)]; simp [hi];intro q _ h; simp [h]
      simp [hi]

    -- avoid he single atomic proof using sum_eq_single.
    simp_rw [he, show ∀ b, (∑ i : Axis, if i=j then Full.wave b x q * Full.wave b y q else 0) = Full.wave b x q * Full.wave b y q by simp, Fintype.sum_bool,if_true,one_mul]
    unfold Full.wave; simp only [Full.corner,Pi.sub_apply,Int.cast_sub,sub_mul,Finset.sum_sub_distrib,Bool.false_eq_true,↓reduceIte]; rw [Real.cos_sub]; ring
  rw [Finset.sum_eq_zero]
  · split_ifs <;> simp_all
  intro c hc; unfold shoot; split_ifs <;> simp_all

def seriesA (a : Atom j) (v : G.ColorIndex) (c : Channel G) (q : E4) := ∑ t:Kind j, degree a t * shoot c q v (a.offset t) a.rotated
def seriesPairs (a : Atom j) (b : Atom k) (u v : G.ColorIndex) (q : E4) := ∑ c : Channel G, seriesA a u c q * seriesA b v c q
lemma pair_rule (a : Atom j) (b : Atom k) (q : E4) (u v : G.ColorIndex) : seriesPairs a b u v q = (if a.rotated=b.rotated then 1 else 0) * inner ℝ (unitColor G u) (unitColor G v) * (∑ t, ∑ s, a.degree t*b.degree s * Full.wave false (a.offset t - b.offset s) q) := by
  let X (t) (q:E4) (s : Kind k) := a.degree t * b.degree s * Full.wave false (a.offset t-b.offset s) q
  let E (c:Channel G) (t : Kind j) (s : Kind k) := a.degree t * b.degree s * (shoot c q u (a.offset t) a.rotated * shoot c q v (b.offset s) b.rotated)
  have he (t s) : ∑ c,E c t s = (if a.rotated=b.rotated then 1 else 0) * inner ℝ (unitColor G u) (unitColor G v) * X t q s := by dsimp [E, X]; rw [←Finset.mul_sum,channel_fusion]; by_cases H:a.rotated=b.rotated <;> split_ifs <;> grind -- rw eq_comm? careful
  calc _ = ∑ c:Channel G,∑ t:Kind j,∑ s:Kind k, E c t s := by
            unfold seriesPairs seriesA; apply Finset.sum_congr rfl; intro c _; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro t _; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _=> by dsimp [E]; ring
       _ = ∑ t,∑ c:Channel G,∑ s,E c t s := Finset.sum_comm
       _ = ∑ t,∑ s,∑ c,E c t s := Finset.sum_congr rfl fun t _=> Finset.sum_comm
       _ = _ := by simp_rw [he,X,Finset.mul_sum]
lemma weight_int (f : Cover) : IntegrableOn (fun q : E4=> (delta q)⁻¹ * Full.wave false f q) cube := by
  apply delta_integrable.mul_bdd (c:=1) ((wave_cont ..).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun q=> Real.abs_cos_le_one _)
lemma pair_sum (a : Atom j) (b : Atom k) : (∫ q in cube, (delta q)⁻¹ * ∑ t : Kind j, ∑ s : Kind k, a.degree t*b.degree s * Full.wave false (a.offset t-b.offset s) q) = ∑ t:Kind j, ∑ s : Kind k, a.degree t*b.degree s * (∫ q in cube, (delta q)⁻¹ * Full.wave false (a.offset t-b.offset s) q) := by
  simp_rw [Finset.mul_sum,mul_left_comm ((delta _:ℝ)⁻¹) (a.degree _*b.degree _)]
  rw [integral_finsetSum _ (fun t _ => integrable_finsetSum _ (fun s _ => (weight_int (a.offset t-b.offset s)).const_mul _))]
  congr 1 with t
  rw [integral_finsetSum _ (fun s _ => (weight_int (a.offset t-b.offset s)).const_mul _)]
  exact Finset.sum_congr rfl fun _ _ => integral_const_mul ..
lemma pair_end (a : Atom j) (b : Atom k) (u v : G.ColorIndex) : volumeFactor * (∫ q in cube, (delta q)⁻¹ * seriesPairs a b u v q) = (if a.rotated=b.rotated then 1 else 0) * inner ℝ (unitColor G u) (unitColor G v) * unroll a b := by
  unfold unroll Cellular.coverLine; simp_rw [pair_rule, mul_left_comm ((delta _:ℝ)⁻¹) ((if a.rotated=b.rotated then 1 else 0)*_), integral_const_mul,pair_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro t _; apply Finset.sum_congr rfl; intro s _;ring
lemma pair_bill (a : Atom j) (b : Atom k) (v w : G.ColorIndex) (h : ℝ) : volumeFactor * (∫ q in cube, (delta q)⁻¹ * (cost a h * cost b h * seriesPairs a b v w q)) = singlePrice a b h (unitColor G v) (unitColor G w) := by
  simp only [mul_left_comm ((delta _:ℝ)⁻¹) (cost a h * _),integral_const_mul]; rw [mul_left_comm volumeFactor, pair_end, singlePrice];split <;>ring
lemma pro_undial (a:Atom j) (h : ℝ) (q : E4) (c : Channel G) (v : G.ColorIndex) : (_root_.id (probes (unitColor G v) a) ∘ₗ chart j a.rot h 0) (material c q) = cost a h * (seriesA a v c q - seriesA (swap a) v c q) := by
  change inner ℝ (unitColor G v) (gain h j • _:G.Color) = _
  rw [real_inner_smul_right]; erw [Atom.core_combine,real_inner_smul_right,inner_sub_right]; simp only [read_cover, seriesA,cost,inner_sum,real_inner_smul_right]; simp_rw [shoot_dual,swap];ring
lemma proc_cont {X : Axis → ℤ} (s : Signed) (c : Channel G) : Continuous (fun q=>_root_.id (chart j s u (0:Cover)) (material c q)) := (wide_base_cont (j:=j) _ (mat_cont c) s (affine s⁻¹ 0 (0:Cover))).const_smul (gain u j)
-- def global bilinear on raw probes by finite dimensional expansion; integral continuous.
lemma series_int (a : Atom j) (g:G.ColorIndex) (c : Channel G) : Continuous (seriesA a g c) := by
  unfold seriesA
  have H t : Continuous (fun q=>a.degree t*shoot c q g (a.offset t) a.rotated) := by
    apply continuous_const.mul
    unfold shoot; split
    exact wave_cont ..
    exact continuous_const
  apply continuous_finsetSum _ (fun i _=>H i)
def mono (a :Atom j) (b: Atom k) (h:ℝ) (u v :G.ColorIndex) (q : E4) := (delta q)⁻¹ * (cost a h * cost b h * seriesPairs a b u v q)
lemma mono_int (a : Atom j) (b : Atom k) (h : ℝ) (u v : G.ColorIndex) : IntegrableOn (mono a b h u v) cube := by
  have hi : Continuous (seriesPairs a b u v) := continuous_finsetSum _ (fun c _=> (series_int _ u c).mul (series_int _ _ c))
  have he := continuous_const.mul (f:=fun (_:E4)=>cost a h*cost b h) hi
  obtain ⟨C,H⟩ := cube_compact.exists_bound_of_continuousOn he.continuousOn; exact delta_integrable.mul_bdd he.aestronglyMeasurable ((ae_restrict_mem cube_compact.measurableSet).mono H)

def coverPair (j k : ℕ) (s t : Signed) (h : ℝ) (q : E4) (P : Module.Dual ℝ (YM.Pert.Bare.Response G j)) (Q : Module.Dual ℝ (YM.Pert.Bare.Response G k)) := (delta q)⁻¹ * ∑ c : Channel G, P (chart j s h 0 (material c q)) * Q (chart k t h 0 (material c q))
lemma eq_cov (a : Atom j) (b : Atom k) (h) (u v : G.ColorIndex) (q:E4) : coverPair j k a.rot b.rot h q (probes (unitColor G u) a) (probes (unitColor G v) b) = mono a b h u v q - mono a (swap b) h u v q - (mono (swap a) b h u v q - mono (swap a) (swap b) h u v q) := by
    rw [coverPair]; unfold mono seriesPairs; simp only [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intros c hc
    rw [show (probes _ _) (chart j _ _ _ (material c q)) = _ from pro_undial a h q c u,show (probes _ _) (chart k _ _ _ (material c q))=_ from pro_undial b h q c v]; unfold cost;ring
set_option maxHeartbeats 200000 in
lemma fx_bill (a : Atom j) (b : Atom k) (h) (u v : G.ColorIndex) : volumeFactor * (∫ q in cube, coverPair j k a.rot b.rot h q (probes (unitColor G u) a) (probes (unitColor G v) b)) = fluxPrice a b h (unitColor G u) (unitColor G v) := by
  let A:=mono a b h u v
  let B:=mono a (swap b) h u v
  let C:=mono (swap a) b h u v
  let D:=mono (swap a) (swap b) h u v
  have M (a : Atom j) (b : Atom k) := mono_int a b h u v
  have ev := MeasureTheory.integral_congr_ae (μ:=volume.restrict cube) (Filter.Eventually.of_forall fun q:E4=>eq_cov a b h u v q)
  have qm : ∀ f g : E4 → ℝ, IntegrableOn f cube → IntegrableOn g cube → (∫ q in cube,f q - g q) = (∫ q in cube,f q) - ∫ q in cube,g q := fun f g => MeasureTheory.integral_sub
  have heq := (qm (A-B) (C-D) ((M _ _).sub (M _ _)) ((M _ _).sub (M _ _))).trans (congrArg₂ Sub.sub (qm A B (M _ _) (M _ _)) (qm C D (M _ _) (M _ _)))
  rw [ev.trans heq]; unfold A B C D
  change volumeFactor * (((∫ q : E4 in cube, mono a b h u v q) - _) - (_ - _)) = _
  simp only [mul_sub,mono,pair_bill]; rfl
end YM.Pert.Align
