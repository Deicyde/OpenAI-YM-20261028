import YM.Next.EXTRACTION.Tails
import YM.Next.FOUNDATIONS.Regular
import YM.Work.B04

/-!
# Finite order calculus of regular germs before masking

At arbitrary healthy `U`, including the boundary. These statements are not smoothness
claims for the indicators or the branch decisions. Keep the ordered left derivatives and
native-site position weights. All growth for changing direction center is displayed; no
assumption that the new center has the old readout!
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Local
open Function Filter Lattice Wilson RG Source Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

variable {G : Gauge} {n : Side}

/-- Smoothness only at the base of the increment chart. -/
abbrev Chart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (f : Config G n → E) (U : Config G n) :=
  ContDiffAt ℝ (k : WithTop ℕ∞) (f ∘ increment U) 0

section Chart
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Change of variables near a configuration in finite dimension. -/
theorem lift_germ (W : E → Config G n) (x : E)
    (h : ∀ l, ContDiffAt ℝ ω (fun y => G.mat (W y l)) x) :
    ∃ q : E → Directions G n, ContDiffAt ℝ ω q x ∧ q x = 0 ∧ W =ᶠ[𝓝 x] increment (W x) ∘ q := by
  let u (l : Edge (Site n)) (y : E) := W y l * (W x l)⁻¹
  have hx (l) : ContDiffAt ℝ ω (G.mat ∘ u l) x := (h l).mul (g:=fun _ => G.mat (W x l)⁻¹) contDiffAt_const
  let q (y : E) (l : Edge (Site n)) := G.plog (G.mat (u l y))
  refine ⟨q, contDiffAt_pi.mpr (fun l => ?_), funext fun l => ?_, ?_⟩
  · exact (show ContDiffAt ℝ ω G.plog ((G.mat ∘ u l) x) by simpa [u] using G.plog_diff).comp x (hx l)
  · simp [q,u]
  suffices he : ∀ l, ∀ᶠ y in 𝓝 x, W y l = increment (W x) (q y) l by
    filter_upwards [eventually_all.mpr he] with y hy
    exact funext hy
  intro l
  have he : ContinuousAt (u l) x :=
    G.continuous_mat.isClosedEmbedding G.mat_injective |>.isInducing.continuousAt_iff.mpr (hx l).continuousAt
  have ht : Tendsto (u l) (𝓝 x) (𝓝 1) := by simpa only [show u l x=1 by simp [u]] using he.tendsto
  filter_upwards [ht.eventually G.plog_right] with y hy
  dsimp only [increment]; rw [show G.lieExp (q y l) = u l y from hy]; simp [u]

theorem chart_comp {k : ℕ} {W : E → Config G n} {x : E} {f : Config G n → Y}
    (hf : Chart k f (W x)) (h : ∀ l, ContDiffAt ℝ ω (fun y => G.mat (W y l)) x) :
    ContDiffAt ℝ (k : WithTop ℕ∞) (f ∘ W) x := by
  obtain ⟨q,hq,hm,he⟩ := lift_germ W x h
  unfold Chart at hf
  rw [← hm] at hf
  exact (hf.comp x (hq.of_le le_top)).congr_of_eventuallyEq (he.fun_comp f)

theorem chart_eventually {k : ℕ} {W : E → Config G n} {x : E} {f : Config G n → Y}
    (hf : Chart k f (W x)) (h : ∀ l, ContDiffAt ℝ ω (fun y => G.mat (W y l)) x) :
    ∀ᶠ y in 𝓝 x, Chart k f (W y) := by
  let Q (p : E × Directions G n) := increment (W p.1) p.2
  have hQ := chart_comp (W:=Q) (x:=(x,0)) (f:=f) (k:=k) (by simpa only [Q,Work.G07.at_zero_increment] using hf) (fun l => by
    simp only [Q, increment, G.mat_mul]
    exact (G.exp_jet.contDiffAt.comp _ ((contDiff_apply ℝ _ _).comp contDiff_snd).contDiffAt).mul (g:=(fun y : E × Directions G n => G.mat (W y.1 l))) ((h l).comp (g:=fun y => G.mat (W y l)) (f:=Prod.fst) (x, (0 : Directions G n)) contDiffAt_fst))
  have ht : Tendsto (fun y : E => (y,(0 : Directions G n))) (𝓝 x) (𝓝 (x,0)) :=
    (continuous_id.prodMk continuous_const).tendsto _
  filter_upwards [ht.eventually (hQ.eventually (by simp))] with y hy
  exact hy.comp 0 (f:=fun v => (y,v)) (contDiffAt_const.prodMk contDiffAt_id)

theorem increment_curve (U : Config G n) (a : Directions G n) (l : Edge (Site n)) (x : ℝ) :
    ContDiffAt ℝ ω (fun t : ℝ => G.mat (increment U (t • a) l)) x := by
  simp only [increment,G.mat_mul,Pi.smul_apply]
  exact (G.exp_jet.comp (contDiff_id.smul contDiff_const)).contDiffAt.mul contDiffAt_const

theorem chart_near {U : Config G n} {k : ℕ} {f : Config G n → Y}
    (hf : Chart k f U) (a : Directions G n) : ∀ᶠ t : ℝ in 𝓝 0, Chart k f (increment U (t • a)) :=
  chart_eventually (by simpa only [zero_smul,Work.G07.at_zero_increment] using hf) (fun l => increment_curve U a l 0)

set_option maxHeartbeats 800000 in
theorem left_congr {f g : Config G n → Y} (l : List (Directions G n)) (U : Config G n)
    (h : f ∘ increment U =ᶠ[𝓝 0] g ∘ increment U) : leftDerivs f l U = leftDerivs g l U := by
  induction l generalizing U with
  | nil => simpa [Work.G07.at_zero_increment,leftDerivs] using h.self_of_nhds
  | cons a l ih =>
    dsimp only [leftDerivs]; apply Filter.EventuallyEq.deriv_eq
    let Q (p : ℝ × Directions G n) := increment (increment U (p.1 • a)) p.2
    have h0 : Q 0 = U := by simp [Q,Work.G07.at_zero_increment]
    obtain ⟨q,hq,hm,he⟩ := lift_germ Q 0 (fun i => by
      simp only [Q, increment,G.mat_mul,Pi.smul_apply]; exact
        ((G.exp_jet.comp ((contDiff_apply ℝ _ _).comp contDiff_snd)).mul
        ((G.exp_jet.comp (contDiff_fst.smul contDiff_const)).mul contDiff_const)).contDiffAt)
    rw [h0] at he
    have hQ : f ∘ Q =ᶠ[𝓝 0] g ∘ Q := (he.fun_comp f).trans ((h.comp_tendsto (hm ▸ hq.continuousAt.tendsto)).trans (he.fun_comp g).symm)
    have ht : Tendsto (fun t : ℝ => (t,(0 : Directions G n))) (𝓝 0) (𝓝 0) := (continuous_id.prodMk continuous_const).tendsto 0
    filter_upwards [ht.eventually (eventually_eventually_nhds.mpr hQ)] with t ht
    change f ∘ Q =ᶠ[𝓝 (t,0)] g ∘ Q at ht
    have hx := ht.comp_tendsto ((continuous_const (y:=t) |>.prodMk continuous_id).tendsto (0 : Directions G n))
    exact ih _ hx

theorem left_sum {k : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Config G n → Y) (U : Config G n)
    (l : List (Directions G n)) (h : ∀ i∈s, Chart k (f i) U) (hl : l.length ≤ k) :
    leftDerivs (∑ i∈s, f i) l U = ∑ i∈s, leftDerivs (f i) l U := by
  induction l generalizing U with
  | nil => simp only [leftDerivs,Finset.sum_apply]
  | cons a l ih =>
    have he : l.length < k := hl
    apply ((HasDerivAt.fun_sum (u:=s) (fun i hi => left_has a he (h i hi))).congr_of_eventuallyEq (f₁:=fun t : ℝ => leftDerivs _ l (increment U (t • a))) ?_).deriv
    have hr : ∀ᶠ t : ℝ in 𝓝 0, ∀ i∈s, Chart k (f i) (increment U (t • a)) :=
      (s.eventually_all).mpr fun i hi => chart_near (h i hi) a
    filter_upwards [hr] with t ht
    exact ih _ ht he.le

theorem left_add {f g : Config G n → Y} {k : ℕ} {U : Config G n}
    (l : List (Directions G n)) (hf : Chart k f U) (hg : Chart k g U) (hl : l.length ≤ k) :
    leftDerivs (f+g) l U = leftDerivs f l U + leftDerivs g l U := by
  induction l generalizing U with
  | nil => rfl
  | cons a l ih =>
    have he : l.length < k := hl
    apply (((left_has a he hf).add (left_has a he hg)).congr_of_eventuallyEq (f₁:=fun t => leftDerivs _ l (increment U (t • a))) ?_).deriv
    filter_upwards [chart_near hf a, chart_near hg a] with t ht ht'
    exact ih ht ht' he.le

theorem left_linear {f : Config G n → Y} {k : ℕ} {U : Config G n} (L : Y →L[ℝ] E)
    (l : List (Directions G n)) (hf : Chart k f U) (hl : l.length ≤ k) :
    leftDerivs (L ∘ f) l U = L (leftDerivs f l U) := by
  induction l generalizing U with
  | nil => rfl
  | cons a l ih =>
    have he : l.length < k := hl
    apply ((L.hasFDerivAt.comp_hasDerivAt _ (left_has a he hf)).congr_of_eventuallyEq (f₁:=fun t => leftDerivs _ l (increment U (t • a))) ?_).deriv
    filter_upwards [chart_near hf a] with t ht
    exact ih ht he.le

theorem left_cons {f : Config G n → Y} {k : ℕ} {U : Config G n}
    (a : Directions G n) (l : List (Directions G n)) (h : Chart k f U) (hl : l.length < k) :
    leftDerivs f (a::l) U = fderiv ℝ (leftDerivs f l ∘ increment U) 0 a := by
  have ht := leftDerivs_chart l 1 (h.of_le (Nat.cast_le.mpr hl))
  have hx : HasDerivAt (fun t : ℝ => t • a) a 0 := by simpa using (hasDerivAt_id' (0:ℝ)).smul_const a
  rw [← show (fun t : ℝ => t • a) 0 = 0 from zero_smul ..] at ht
  simpa only [leftDerivs,comp_def,zero_smul] using ((ht.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hx).deriv

theorem left_homogeneous {f : Config G n → Y} {k : ℕ} {U : Config G n}
    (l : List (Directions G n)) (h : Chart k f U) (hl : l.length ≤ k) (r : ℝ) :
    leftDerivs f (l.map (r • ·)) U = r^l.length • leftDerivs f l U := by
  induction l generalizing U with
  | nil => simp only [List.map_nil,List.length_nil,pow_zero,one_smul]
  | cons a l ih =>
    have he : l.length < k := hl
    have ht : HasDerivAt (fun t : ℝ => leftDerivs f (l.map (r • ·)) (increment U (t • (r • a))))
        (r^l.length • leftDerivs f ((r • a)::l) U) 0 := by
      apply ((left_has (r • a) he h).const_smul (r^l.length)).congr_of_eventuallyEq
      filter_upwards [chart_near h (r • a)] with t ht
      exact ih ht he.le
    rw [List.map_cons,leftDerivs,ht.deriv,left_cons (r • a) l h he, map_smul, smul_smul, ← left_cons a l h he, List.length_cons,pow_succ]

variable {Z : Type*} [NormedRing Z] [NormedAlgebra ℝ Z]

theorem left_first_mul {f g : Config G n → Z} {U : Config G n} (a : Directions G n)
    (hf : Chart 1 f U) (hg : Chart 1 g U) :
    leftDerivs (f*g) [a] U = leftDerivs f [a] U * g U + f U * leftDerivs g [a] U := by
  have he := ((left_has a (l:=[]) (by simp) hf).mul (left_has a (l:=[]) (by simp) hg)).deriv
  exact he.trans (by simp only [zero_smul, Work.G07.at_zero_increment,leftDerivs])

/-- Pointwise ordered-derivative Leibniz budget under C^k germ control only. -/
theorem left_mul_bound {D : Directions G n → Prop} {f g : Config G n → Z} {k : ℕ} {U : Config G n}
    {a b : ℝ} (hf : Chart k f U) (hg : Chart k g U)
    (hc : ∀ l : List (Directions G n), l.length ≤ k → (∀ v∈l, D v) → ‖leftDerivs f l U‖ ≤ a)
    (hc' : ∀ l : List (Directions G n), l.length ≤ k → (∀ v∈l, D v) → ‖leftDerivs g l U‖ ≤ b) :
    ∀ l : List (Directions G n), l.length ≤ k → (∀ v∈l, D v) → ‖leftDerivs (f*g) l U‖ ≤ 2^l.length * (a*b) := by
  intro l hl hD
  induction l using List.reverseRecOn generalizing f g k with
  | nil => simpa [leftDerivs] using (norm_mul_le (f U) (g U)).trans (mul_le_mul
      (hc [] hl hD) (hc' [] hl hD) (norm_nonneg _) ((norm_nonneg _).trans (hc [] hl hD)))
  | append_singleton l A ih =>
    have he : l.length+1 ≤ k := by simpa using hl
    have H (w : Config G n → Z) (hw : Chart k w U) : Chart l.length (leftDerivs w [A]) U :=
      leftDerivs_chart _ l.length (hw.of_le (Nat.cast_le.mpr (Nat.add_comm .. ▸ he)))
    have hN (w : Config G n → Z) (c : ℝ) (hw : ∀ l : List (Directions G n), l.length ≤ k → (∀ v∈l, D v) → ‖leftDerivs w l U‖ ≤ c)
        (l' : List (Directions G n)) (hl' : l'.length ≤ l.length) (he' : ∀ v∈l', D v) :
        ‖leftDerivs (leftDerivs w [A]) l' U‖ ≤ c := by
      rw [← Work.G07.left_append]; refine hw _ (by simp; omega) ?_
      intro v hv; rcases List.mem_append.mp hv with h|h
      · exact he' _ h
      · exact hD _ (List.mem_append_right _ h)
    have ht : leftDerivs (f*g) [A] ∘ increment U =ᶠ[𝓝 0]
        (leftDerivs f [A]*g + f*leftDerivs g [A]) ∘ increment U := by
      have hk : (1:ℕ) ≤ k := by omega
      have h' (w : Config G n → Z) (hw : Chart k w U) : ∀ᶠ x in 𝓝 0, Chart 1 w (increment U x) :=
        chart_eventually (by rw [Work.G07.at_zero_increment]; exact hw.of_le (Nat.cast_le.mpr hk))
          fun i => by
            simp only [increment,G.mat_mul]; exact ((G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const).contDiffAt
      filter_upwards [h' f hf,h' g hg] with t ht ht'; exact left_first_mul A ht ht'
    rw [Work.G07.left_append,left_congr l U ht]
    have hle : l.length ≤ k := by omega
    have hsf := hf.of_le (Nat.cast_le.mpr hle)
    have hsg := hg.of_le (Nat.cast_le.mpr hle)
    have hd : ∀ v∈l, D v := fun v hv => hD v (by simp [hv])
    rw [left_add l ((H f hf).mul hsg) (hsf.mul (H g hg)) (le_refl l.length)]
    apply (norm_add_le ..).trans
    exact (add_le_add
      (ih (k:=l.length) (H _ hf) hsg (hN _ a hc) (fun i hi => hc' i (hi.trans hle)) le_rfl hd)
      (ih (k:=l.length) hsf (H _ hg) (fun i hi => hc i (hi.trans hle)) (hN _ b hc') le_rfl hd)).trans_eq (by simp; ring)
end Chart

section Regular
variable {B : BudgetPoint} {X Y : Support n} {f g : Config G n → ℂ} {o : Site n} {a b : ℝ}

theorem regular_const (c : ℂ) : B.Regular X (fun _ : Config G n => c) := by
  exact ⟨fun _ _ _ => rfl, measurable_const, fun _ _ => rfl, fun _ _ => contDiffAt_const,
    fun U _ A _ hl => left_has (U:=U) A hl (f:=fun _ => c) contDiffAt_const⟩

theorem bound_const (c : ℂ) : B.supBounds o X (fun _ : Config G n => c) ‖c‖ := by
  refine ⟨norm_nonneg _,fun U _ l _ _ => ?_⟩; rw [Work.G07.left_const]; split <;> simp

theorem bound_weaken (h : B.supBounds o X f a) (he : a ≤ b) : B.supBounds o X f b :=
  ⟨h.1.trans he,fun U hu l hl hd => (h.2 U hu l hl hd).trans he⟩

theorem bound_rescale_dirs (h : B.supBounds o X f a) (hf : B.Regular X f)
    (U : Config G n) (hU : Healthy B.threshold X U) (l : List (Directions G n)) (hl : l.length ≤ B.order)
    (r : ℝ) (hr : 0 < r)
    (hd : ∀ v∈l, ∀ e, ‖v e‖ ≤ r*(B.threshold * (1+(separation e.1 o : ℝ))^B.power)) :
    ‖leftDerivs f l U‖ ≤ r^l.length * a := by
  let l' := l.map (r⁻¹ • ·)
  have h' : ‖leftDerivs f l' U‖ ≤ a := by
    apply h.2 U hU l' (by simpa [l'])
    simp only [l',List.forall_mem_map]
    intro v hv e; rw [Pi.smul_apply,norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr).le]
    exact (mul_le_mul_of_nonneg_left (hd _ hv e) (inv_pos.mpr hr).le).trans_eq (by simp [← mul_assoc,hr.ne'])
  rw [show l = l'.map (r • ·) from Eq.symm (by simp [l',List.map_map,comp_def,smul_smul, hr.ne']),
    left_homogeneous l' (hf.smooth U hU) (by simpa [l'] using hl), norm_smul, Real.norm_of_nonneg (pow_pos hr _).le]
  simp only [List.length_map]; exact mul_le_mul_of_nonneg_left h' (pow_pos hr _).le

theorem bound_shift (h : B.supBounds o X f a) (hf : B.Regular X f) (b : Site n) :
    B.supBounds b X f (((1+(separation o b : ℝ))^B.power)^B.order * a) := by
  let r : ℝ := 1+separation o b
  have hr : 1 ≤ r := by simp [r]
  refine ⟨by positivity [h.1], fun U hu l hl hd => ?_⟩
  refine (bound_rescale_dirs h hf U hu l hl (r^B.power) (pow_pos (lt_of_lt_of_le zero_lt_one hr) _) ?_).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (one_le_pow₀ hr) hl) h.1)
  intro v hv e
  apply (hd v hv e).trans (le_trans (mul_le_mul_of_nonneg_left ?_ B.threshold_pos.le) (b:=B.threshold*(r^B.power*(1+(separation e.1 o : ℝ))^B.power)) (le_of_eq (mul_left_comm ..)))
  rw [← mul_pow]; refine pow_le_pow_left₀ (by positivity) ?_ _
  dsimp only [r]; have he : (separation e.1 b : ℝ) ≤ (separation e.1 o : ℝ)+(separation o b : ℝ) := by exact_mod_cast separation_triangle e.1 o b
  nlinarith [show (0:ℝ) ≤ (separation o b : ℝ)*(separation e.1 o : ℝ) from by positivity]

theorem regular_bar (h : B.Regular X f) : B.Regular X (star f) := by
  let L := (starL' ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap
  have ht (U) (hu : Healthy B.threshold X U) : Chart B.order (star f) U := L.contDiff.contDiffAt.comp _ (h.smooth U hu)
  exact ⟨fun _ _ he => congr_arg star (h.sites _ _ he), L.continuous.measurable.comp h.borel,
    fun k U => congr_arg star (h.symmetry k U), ht,fun U hu v _ hl => left_has v hl (ht _ hu)⟩

theorem bound_bar (h : B.Regular X f) (hc : B.supBounds o X f a) : B.supBounds o X (star f) a := by
  refine ⟨hc.1, fun U hu l hl hd => ?_⟩
  change ‖leftDerivs ((starL' ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap ∘ f) l U‖ ≤ _
  rw [left_linear (starL' ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap l (h.smooth U hu) hl]
  simpa using hc.2 U hu l hl hd

theorem regular_mul (h : B.Regular X f) (he : B.Regular X g) : B.Regular X (f*g) := by
  have ht (U) (hu : Healthy B.threshold X U) : Chart B.order (f*g) U := (h.smooth U hu).mul (he.smooth U hu)
  exact ⟨fun _ _ hx => congr_arg₂ (· * ·) (h.sites _ _ hx) (he.sites _ _ hx), h.borel.mul he.borel,
    fun _ _ => congr_arg₂ (· * ·) (h.symmetry _ _) (he.symmetry _ _), ht, fun U hu A _ hl => left_has A hl (ht _ hu)⟩

theorem bound_mul (h : B.Regular X f) (he : B.Regular X g) (hc : B.supBounds o X f a) (hd : B.supBounds o X g b) :
    B.supBounds o X (f*g) (2^B.order * (a*b)) :=
  ⟨mul_nonneg (by positivity) (mul_nonneg hc.1 hd.1), fun U hu l hl hD => (left_mul_bound (h.smooth U hu) (he.smooth U hu) (hc.2 U hu) (hd.2 U hu) l hl hD).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hl) (mul_nonneg hc.1 hd.1))⟩

end Regular
end YM.Push.Local
