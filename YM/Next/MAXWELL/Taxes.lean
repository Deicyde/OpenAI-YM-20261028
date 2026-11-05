import YM.Next.MAXWELL.Double
import YM.Next.MAXWELL.Repeat
import YM.Work.A01.Support


/-!
# Stress shell-flux for arbitrary Wick polynomials

Universal compact collar laws, complex values, all spectator words;
both actual fluxes and the supplementary dilation charge. Prove first
at polynomial level so no question of whether sources or resulting
expressions are invariant/separated-null when using Wick contractions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory
open WaveOn Wick
open scoped ContDiff Topology BigOperators InnerProductSpace

variable {G : Gauge} {j l d m n : ℕ}

/-- Shared assembly. We'll instantiate this for all three motions. -/
structure Motion {x : E4} (v : Drive) (T : Engine G l) (χ : E4 → ℝ) : Prop where
  symm : Killing v
  collide (p q : Factor G) : singleFlux v χ (pulse p.2 x) (pulse q.2 x) = 0
  flux (p q : Factor G) (y : E4) : x≠y → y∉tsupport χ → singleFlux v χ (pulse p.2 x) (pulse q.2 y)=
    - K (T p.1 p.2) q.2 x y

section Motion
variable {χ : E4 → ℝ} {x : E4} (hχ : ContDiff ℝ ∞ χ) (Hχ : HasCompactSupport χ) (hw : χ =ᶠ[𝓝 x] fun _ => 1)
include hχ Hχ hw

lemma straight_motion (a : Axis) : Motion (x:=x) (drift a) (glide G (basis a)) χ where
  symm := drift_K a
  collide p q := two_flux_zero hχ Hχ hw (drift_K a) 0 (by decide) (fun _ _ _ _ => by simp [drift]) p.2 q.2
  flux p q y he ht := by
    rw [drift_flux isOpen_compl_singleton (pulse_wave q.2 y) p.2 a hχ Hχ (fun z hz => fun h : z=y => ht (h ▸ hz)) hw]
    rw [K_symmetric _ _ he, K_sample _ _ (Ne.symm he)]; rfl

private lemma centers_collide (p q : Factor G) (u : M4) (h : Killing (fromCenter u x)) :
    singleFlux (fromCenter u x) χ (pulse p.2 x) (pulse q.2 x) = 0 := by
  refine two_flux_zero hχ Hχ hw h 1 le_rfl ?_ _ _
  intro t ht i z; unfold fromCenter
  simp only [add_sub_cancel_left,pow_one]; exact map_smul (row u i) t z

lemma rotational_motion (a : Ortho.Skew) : Motion (G:=G) (l:=0) (x:=x) (fromCenter a.val x) (wheel G a) χ where
  symm := skew_K a x
  collide p q := centers_collide hχ Hχ hw p q _ (skew_K a x)
  flux p q y he ht := by
    rw [angular_flux isOpen_compl_singleton (pulse_wave q.2 y) p.2 a hχ Hχ (fun z hz => fun h : z=y => ht (h ▸ hz)) hw]
    rw [K_symmetric _ _ he, K_sample _ _ (Ne.symm he)]; rfl

lemma radial_motion : Motion (G:=G) (l:=0) (x:=x) (fromCenter 1 x) (metric G) χ where
  symm := radial_K x
  collide p q := centers_collide hχ Hχ hw p q _ (radial_K x)
  flux p q y he ht := by
    rw [radial_flux isOpen_compl_singleton (pulse_wave q.2 y) p.2 hχ Hχ (fun z hz => fun h : z=y => ht (h ▸ hz)) hw]
    rw [K_symmetric _ _ he, K_sample _ _ (Ne.symm he)];
    change _ = -sample (((p.1:ℝ)+2) • p.2) _ _; rw [sample_smulLeg,neg_mul]
end Motion

lemma flux_invariant {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] (χ : E4 → ℝ) (A B : Axis → E4 → M)
    (h : ∀ i y, y ∈ tsupport (fderiv ℝ χ) → A i y=B i y) : exportFlux A χ=exportFlux B χ := by
  unfold exportFlux; congr 1; apply Finset.sum_congr rfl; intro a _
  apply integral_congr_ae; apply Eventually.of_forall; intro y; dsimp only; by_cases hw : y∈tsupport (fderiv ℝ χ)
  · rw [h a y hw]
  rw [image_eq_zero_of_notMem_tsupport (x:=y) (f := grad a χ) (fun hh => hw (gradient_part χ a hh)),zero_smul,zero_smul]

lemma flux_series {ι M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [CompleteSpace M]
    {χ : E4 → ℝ} (hχ : ContDiff ℝ ∞ χ) (Hχ : HasCompactSupport χ) (v : Finset ι)
    (F : ι → Axis → E4 → M) (H : ∀ i a y, y ∈ tsupport (fderiv ℝ χ) → ContinuousAt (F i a) y) :
    exportFlux (fun a y => ∑ i ∈ v, F i a y) χ = ∑ i ∈ v, exportFlux (F i) χ := by
  unfold exportFlux
  simp only [Finset.smul_sum]; simp_rw [integral_finsetSum v fun i _ => shell_cost hχ Hχ (H i _) _]
  rw [Finset.sum_comm]; rw [Finset.sum_neg_distrib]

lemma flux_scalar (χ : E4 → ℝ) (f : Axis → E4 → ℂ) (z : ℂ) :
    exportFlux (fun a x => z*f a x) χ=z*exportFlux f χ := by
  have he (a) (x : E4) : grad a χ x • (z * f a x)=z*(grad a χ x • f a x) := by rw [mul_smul_comm]
  unfold exportFlux; simp_rw [he, integral_const_mul, ← Finset.mul_sum, mul_neg]

lemma flux_complex (χ : E4 → ℝ) (f : Axis → E4 → ℝ) (z : ℂ) :
    exportFlux (fun a x => (f a x:ℂ)*z) χ=(↑(exportFlux f χ:ℝ):ℂ)*z := by
  rw [show (fun (a : Axis) (x : E4) => (f a x:ℂ)*z) = (fun a x => z*(f a x:ℂ)) from
    funext fun a => funext fun x => mul_comm ..]
  rw [flux_scalar,mul_comm z]; congr 1
  unfold exportFlux; push_cast
  simp_rw [Complex.real_smul,← Complex.ofReal_mul, integral_complex_ofReal, smul_eq_mul]

section Setup
variable {χ : E4 → ℝ} {x : Points (n+1)} (hx : x∈conf (n+1)) (w : Table.Window x χ)
  {v : Drive} {T : Engine G l} (hT : Motion (x:=x 0) v T χ)

def stressRead (x : Points n) (v : Drive) (F : Fin n → WickPol G) (a : Axis) (y : E4) : ℂ :=
    ∑ b : Axis, v b y • bookend x y F (polStress G a b)

include hx w
lemma petal_cost (a b : Axis) (p : Fin (n+1) → WickPol G) (k : Killing v) {y : E4} (hy : y ∈ tsupport (fderiv ℝ χ)) :
    ContinuousAt (fun y => v b y • bookend x y p (polStress G a b)) y := by
  apply ContinuousAt.smul ((k.diff _).continuous.continuousAt)
  have hp := Work.A01.window_separated hx w hy
  have he : Continuous fun y : E4 => Points.cons y x := by
    unfold Points.cons points; fun_prop
  simp_rw [book_eval]
  exact (moment_smooth _ hp).continuousAt.comp (x:=y) (f := fun y => Points.cons y x) he.continuousAt

lemma petal_green (a b : Axis) (p : Fin (n+1) → WickPol G) (k : Killing v) :
    Integrable fun y => grad a χ y • (v b y • bookend x y p (polStress G a b)) :=
  shell_cost w.1 w.2.1 (fun _ hy => petal_cost hx w a b p k hy) a

include hT

/-- Sum over all three cases of the double extraction. -/
theorem fees {ι : Type*} (L : List ι) (u : ι → Fin (n+1)) (Q : ι → Factor G) :
    exportFlux (stressRead x v (bag u Q L)) χ = -moment G x (update (bag u Q L) 0
      (rewired T (bag u Q L 0))) := by
  classical
  let B := tsupport (fderiv ℝ χ)
  let R := pairCost (strength x u Q)
  let D := subEdge x u Q T 0
  let f (i : ι) := pulse (Q i).2 (x (u i))
  let I (i j : ι) (s : List ι) (a : Axis) (y : E4) := ((current v (f i) (f j) a y:ℝ):ℂ) * R s
  have he (a : Axis) (y : E4) (hy : y ∈ B) : stressRead x v (bag u Q L) a y =
      1/2 * pulls L (fun i p => pulls p (fun j s => I i j s a y)) := by
    have he := Work.A01.window_separated hx w hy
    simp_rw [stressRead, reads_debit x Q u L he,I,R,f,current,pulls];
    simp only [Finset.mul_sum,Finset.smul_sum,Complex.real_smul,Complex.ofReal_sum, Finset.sum_mul, Complex.ofReal_mul]
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro k _; ring
  have hf (i j s a) (y : E4) (hy : y ∈ B) : ContinuousAt (I i j s a) y := by
    have hs (i : ι) : y ≠ x (u i) := (show Injective (Points.cons y x).ofLp from
      Work.A01.window_separated hx w hy).ne (Ne.symm (Fin.succ_ne_zero _))
    exact (Complex.continuous_ofReal.continuousAt.comp (current_diff hT.symm a
      (fun a b => (pulse_wave ..).smooth a b y (hs i)) (fun a b => (pulse_wave ..).smooth a b y (hs j))).continuousAt).mul continuousAt_const
  rw [flux_invariant χ _ _ he,flux_scalar]
  have ht : exportFlux (fun a y => pulls L (fun i p => pulls p (fun j s => I i j s a y))) χ =
      pulls L (fun i p => pulls p (fun j s => (singleFlux v χ (f i) (f j) : ℂ) * R s)) := by
    unfold pulls; rw [flux_series w.1 w.2.1];
    · apply Finset.sum_congr rfl; intro i _; dsimp only; rw [flux_series w.1 w.2.1];
      · exact Finset.sum_congr rfl fun j _ => flux_complex χ _ _
      exact fun i a y hy => hf _ _ _ a y hy
    intro i a y hy; exact tendsto_finsetSum _ fun j _ => hf _ _ _ a y hy
  have hb i (h : 0≠u i) : x (u i) ∉ tsupport χ := by
    have ht := w.2.2.2 ((u i).pred h.symm); rwa [Fin.succ_pred] at ht
  have hs i j (h : 0=u i) (w : 0≠u j) : (↑(singleFlux v χ (f i) (f j)):ℂ) = -(D i j+D j i) := by
    have ht : x 0 ≠ x (u j) := (show Injective x.ofLp from hx).ne w
    have he := hT.flux (Q i) (Q j) (x (u j)) ht (hb j w)
    unfold f D subEdge
    rw [if_pos h,if_neg w, ← h, he, Complex.ofReal_neg,add_zero]; congr 1
    exact (link_eq _ _ (relay T (Q i)) (Q j) ht).symm
  have ha (i j : ι) : (↑(singleFlux v χ (f i) (f j)) : ℂ) = -(D i j+D j i) := by
    by_cases h : 0=u i
    · by_cases ht : 0=u j
      · unfold f D subEdge; rw [if_pos h,if_pos ht,← h,← ht,hT.collide (Q i) (Q j)]
        simp only [beam,← h,← ht,link_zero]; simp
      exact hs i j h ht
    by_cases ht : 0=u j
    · rw [add_comm,← hs j i ht h]
      unfold singleFlux; congr 2
      funext a y
      exact Finset.sum_congr rfl fun b _ => congr_arg (fun z : ℝ => v b y * z) (cross_comm ..)
    unfold D subEdge; rw [if_neg h,if_neg ht,add_zero, neg_zero]
    have Hp : tsupport χ ⊆ ({x (u i)}ᶜ ∩ {x (u j)}ᶜ : Set E4) := fun y hy => ⟨fun e : y=x (u i) => hb i h (e ▸ hy),
      fun e : y=x (u j) => hb j ht (e ▸ hy)⟩
    rw [sourcefree_flux hT.symm w.1 w.2.1 Hp (f := f i) (g:= f j) (wave_mono inter_subset_left (pulse_wave ..))
      (wave_mono inter_subset_right (pulse_wave ..)) (isOpen_compl_singleton.inter isOpen_compl_singleton), Complex.ofReal_zero]
  rw [ht]; simp_rw [ha, neg_mul]
  rw [bag_relay _ _ L _ T hx]
  have heq := pulls_twice L fun i j s => D i j*R s
  dsimp only [R,D] at heq ⊢
  unfold pulls at *; simp_rw [add_mul, Finset.sum_neg_distrib,Finset.sum_add_distrib,heq]; ring

/-- General Wick identities. The integral is the actual insertion of the
composite stress; this proof has included the terms with no marked
contraction and with both, not just retaining a single-legged summand. -/
theorem moment_force (p : Fin (n+1) → WickPol G) :
    exportFlux (stressRead x v p) χ = -moment G x (update p 0 (rewired T (p 0))) := by
  classical
  obtain ⟨L,hL⟩ := substitution x 0 (rewired T).toLinearMap
  rw [show moment G x (update p 0 (rewired T (p 0)))=L p from (hL p).symm,
    Multilabel.expansion (fun _ => monBasis G) L]
  let F (i : Powers G (n+1)) := fun j => monBasis G (i j)
  let B := Fintype.piFinset (fun i => ((monBasis G).repr (p i)).support)
  let c (i : Powers G (n+1)) := ∏ j, (monBasis G).repr (p j) (i j)
  have he (a : Axis) (y : E4) : stressRead x v p a y = ∑ i ∈ B, c i * stressRead x v (F i) a y := by
    have hs (q : WickPol G) : bookend x y p q = ∑ i ∈ B, c i • bookend x y (F i) q := by
      let U : MultilinearMap ℂ (fun _ : Fin (n+1) => WickPol G) ℂ := (moment G (Points.cons y x)).curryLeft q
      have hh f : bookend x y f q=U f := book_eval ..
      simp_rw [hh]; exact Multilabel.expansion _ U p
    simp_rw [stressRead,hs,Finset.smul_sum,Complex.real_smul,smul_eq_mul,Finset.mul_sum]
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro b _; ring
  rw [show stressRead x v p = _ from funext fun i => funext (he i), flux_series w.1 w.2.1];
  · rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _
    change exportFlux (fun a y => c i * stressRead x v (F i) a y) χ = -(c i * L (F i))
    rw [flux_scalar]
    obtain ⟨s,h⟩ := power_bag i
    rw [show F i=bag Prod.fst Prod.snd s from h.symm,fees hx w hT s,hL,mul_neg]; rfl
  intro i a y hy; apply ContinuousAt.mul continuousAt_const;
  exact tendsto_finsetSum _ fun b _ => petal_cost hx w a b _ hT.symm hy
end Setup
end YM.Maxwell.Free
