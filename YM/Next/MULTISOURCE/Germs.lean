import YM.Shoot.Criteria
import YM.Work.G07.Calculus



/-! Local chart math to actually ADD weighted Taylor coefficients in a scalar bank.

At the good-set boundary, the definition of iterated left derivatives
may use off-mask values! Never assert additivity from differentiability only
on an interior. Derive exactly what we need from the `ContDiffAt` germ.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Multi.Puff
open RG Lattice Wilson Function Filter
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {n : Side} {G : Gauge} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

abbrev World (G : Gauge) (n : Side) := Edge (Site n) → G.Mat
def showU (U : Config G n) : World G n := G.mat ∘ U
lemma visible : Continuous (showU (G:=G) (n:=n)) :=
    continuous_pi fun i => G.continuous_mat.comp (continuous_apply i)

lemma inc_zero (U : Config G n) : increment U 0 = U := Work.G07.at_zero_increment U
lemma inc_tr (U : Config G n) : Continuous (increment U) := by unfold increment; fun_prop

lemma swing (U : Config G n) (A : Directions G n) : Tendsto (fun t : ℝ => increment U (t • A)) (𝓝 0) (𝓝 U) := by
  have he : Continuous (fun t : ℝ => increment U (t • A)) := (inc_tr U).comp (continuous_id.smul continuous_const)
  simpa only [zero_smul,inc_zero] using he.tendsto 0

def trench (U : Config G n) (χ : World G n) : Directions G n :=
    fun i => G.plog (χ i * G.mat (U i)⁻¹)
@[simp] lemma trench_at (U : Config G n) : trench U (showU U)=0 := by
  funext i; simp [trench, showU, - Gauge.mat_mul]
lemma trench_slides (U : Config G n) : ContDiffAt ℝ ω (trench U) (showU U) := by
  refine contDiffAt_pi.mpr fun i => ?_
  let f (v : World G n) := v i * G.mat (U i)⁻¹
  have he : ContDiffAt ℝ ω G.plog (f (showU U)) := by simp only [f, showU,comp_apply,← G.mat_mul,mul_inv_cancel,G.mat_one]; exact G.plog_diff
  exact he.comp _ ((contDiffAt_apply ..).mul contDiffAt_const : ContDiffAt ℝ ω f (showU U))

lemma trench_main (U : Config G n) : ∀ᶠ V in 𝓝 U, increment U (trench U (showU V)) = V := by
  have he (i : Edge (Site n)) : Tendsto (fun V : Config G n => V i*(U i)⁻¹) (𝓝 U) (𝓝 1) := by
    have hf : Continuous (fun V : Config G n => V i * (U i)⁻¹) := (continuous_apply i).mul continuous_const
    simpa only [mul_inv_cancel] using hf.tendsto U
  have hh := eventually_all.mpr (fun i => (he i).eventually G.plog_right)
  filter_upwards [hh] with V hV; funext i
  simpa [trench,increment,showU,← G.mat_mul] using congrArg (· * U i) (hV i)

lemma exposed (U : Config G n) : ContDiff ℝ ω (showU ∘ increment U) := by
  refine contDiff_pi.mpr fun i => ?_
  simp only [showU, Function.comp_apply,increment,G.mat_mul]
  have ht : ContDiff ℝ ω (fun v : Directions G n => G.mat (G.lieExp (v i))) := G.exp_jet.comp (f:=fun v : Directions G n => v i) (contDiff_apply ..)
  exact ht.mul contDiff_const

-- Chart germ may use ordinary ambient coordinates
def Crest (k : ℕ) (F : Config G n → X) (U : Config G n) := ∃ g : World G n → X,
    ContDiffAt ℝ (k : ℕ∞) g (showU U) ∧ F =ᶠ[𝓝 U] g ∘ showU

lemma into (k : ℕ) {U : Config G n} (F : Config G n→X) (he : ContDiffAt ℝ (k:ℕ∞) (F ∘ increment U) 0) : Crest k F U := by
  refine ⟨(F ∘ increment U) ∘ trench U,?_,?_⟩
  · refine ContDiffAt.comp _ ?_ ((trench_slides U).of_le le_top); rwa [trench_at U]
  filter_upwards [trench_main U] with V hv
  simp [Function.comp_apply,hv]

lemma Crest.near {k : ℕ} {F : Config G n → X} {U} (h : Crest k F U) :
    ∀ᶠ V in 𝓝 U, Crest k F V := by
  obtain ⟨g,hg,H⟩:=h
  have he := (visible.tendsto U).eventually (hg.eventually (by simp))
  have hK : ∀ᶠ V in 𝓝 U, F =ᶠ[𝓝 V] g ∘ showU := eventually_eventually_nhds.mpr H
  filter_upwards [he,hK] with V hV hv
  exact ⟨_,hV,hv⟩

lemma Crest.germ {k : ℕ} {F : Config G n → X} {U} (h : Crest k F U) :
    ContDiffAt ℝ (k:ℕ∞) (F ∘ increment U) 0 := by
  obtain ⟨g,hg,H⟩:=h
  have he := H.comp_tendsto (show Tendsto (increment U) (𝓝 0) (𝓝 U) from by
    simpa [inc_zero] using (inc_tr U).tendsto 0)
  refine ContDiffAt.congr_of_eventuallyEq (f:=g ∘ showU ∘ increment U) ?_ he
  refine ContDiffAt.comp _ ?_ ((exposed U).contDiffAt.of_le le_top)
  rwa [Function.comp_apply,inc_zero]

-- multiplicative matrix increments off-shell

def dance (A : Directions G n) (y : World G n) (t : ℝ) : World G n :=
    fun i => G.mat (G.lieExp (t • A i)) * y i
@[simp] lemma dance_zero (A : Directions G n) (y : World G n) : dance A y 0=y := by
  funext i; simp [dance]
lemma dance_tr (A : Directions G n) : ContDiff ℝ ω (Function.uncurry (dance A)) := by
  refine contDiff_pi.mpr fun i => ?_
  have he : ContDiff ℝ ω (fun v : World G n × ℝ => G.mat (G.lieExp (v.2 • A i))) :=
    G.exp_jet.comp (f:=fun v : World G n × ℝ => v.2 • A i) (contDiff_snd.smul contDiff_const)
  exact he.mul ((contDiff_apply ℝ G.Mat i).comp contDiff_fst)
lemma dance_U (U : Config G n) (A : Directions G n) (t : ℝ) :
    showU (increment U (t • A)) = dance A (showU U) t := by
  funext i; simp only [increment,showU,Function.comp_apply,dance,Pi.smul_apply,G.mat_mul]

lemma Crest.falls {k : ℕ} {F : Config G n → X} {U} (h : Crest (k+1) F U) (A : Directions G n) :
    Crest k (leftDerivs F [A]) U := by
  obtain ⟨g,hg,H⟩ := h
  let f (y : World G n) := fun t : ℝ => g (dance A y t)
  refine ⟨fun V => deriv (f V) 0,?_,?_⟩
  · have ht : ContDiffAt ℝ (↑((k+1:ℕ) : ℕ∞) : WithTop ℕ∞) (uncurry f) (showU U, 0) :=
      ContDiffAt.comp (f:=uncurry (dance A)) (g:=g) _ (by simp; exact hg) ((dance_tr A).contDiffAt.of_le le_top)
    have he : ContDiffAt ℝ (k:ℕ∞) (fun V => fderiv ℝ (f V) 0) (showU U) :=
      ht.fderiv (g:=fun _ => 0) contDiffAt_const (by simp)
    exact he.clm_apply contDiffAt_const
  have he : ∀ᶠ V in 𝓝 U, F =ᶠ[𝓝 V] g ∘ showU := eventually_eventually_nhds.mpr H
  filter_upwards [he] with V hV
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [(hV.comp_tendsto (swing V A))] with t ht
  simpa only [Function.comp_apply,dance_U,f,leftDerivs] using ht

lemma Crest.subcrest {k : ℕ} {F : Config G n → X} {U} (A : List (Directions G n)) (H : Crest (k + A.length) F U) :
    Crest k (leftDerivs F A) U := by
  induction A using List.reverseRecOn generalizing F with
  | nil => exact H
  | append_singleton l a ih =>
    rw [Work.G07.left_append]
    exact ih ((show Crest ((k+l.length)+1) F U from by simpa [Nat.add_assoc] using H).falls a)

lemma Crest.line {k : ℕ} {F : Config G n → X} {U} (h : Crest k F U) (A : List (Directions G n)) (ht : A.length < k)
    (i : Directions G n) : DifferentiableAt ℝ (fun t : ℝ => leftDerivs F A (increment U (t • i))) 0 := by
  let d := k-A.length
  have hd : 0 < d := Nat.sub_pos_of_lt ht
  have he := Crest.germ (k:=d) (F:=leftDerivs F A) (U:=U) (Crest.subcrest A (show Crest (d+A.length) _ _ by
    rw [Nat.sub_add_cancel ht.le]; exact h))
  have hp : DifferentiableAt ℝ (leftDerivs F A ∘ increment U) ((0:ℝ) • i) := by rw [zero_smul]; exact he.differentiableAt (by simp [hd.ne'])
  exact hp.comp (f:=fun t => t • i) 0 (by fun_prop)

lemma Crest.sum_at {k : ℕ} {F F' : Config G n → X} (A : List (Directions G n)) (hl : A.length ≤ k) (U : Config G n)
    (h : Crest k F U) (h' : Crest k F' U) :
    leftDerivs (F+F') A U = leftDerivs F A U + leftDerivs F' A U := by
  induction A generalizing U with
  | nil => rfl
  | cons i l ih =>
    have hk : l.length < k := hl
    let f (t : ℝ) := increment U (t • i)
    have he : (leftDerivs (F+F') l) ∘ f =ᶠ[𝓝 0] (fun t => leftDerivs F l (f t)+leftDerivs F' l (f t)) := by
      filter_upwards [(swing U i).eventually h.near,(swing U i).eventually h'.near] with V hV hV'
      exact ih hk.le _ hV hV'
    exact he.deriv_eq.trans (deriv_add (h.line l hk i) (h'.line l hk i))

lemma combine {P : BudgetPoint} {V : Support n} {F H : Config G n → ℂ} (h : P.Regular V F) (he : P.Regular V H) :
    P.Regular V (F+H) := by
  refine ⟨fun U X hx => by simp only [Pi.add_apply,h.sites U X hx,he.sites U X hx],h.borel.add he.borel,
    fun k U => by simp only [Pi.add_apply,h.symmetry k U,he.symmetry k U],fun U hh => (h.smooth U hh).add (he.smooth U hh),?_⟩
  intro U hh i l hl
  exact ((into P.order (F+H) ((h.smooth U hh).add (he.smooth U hh))).line l hl i).hasDerivAt

lemma balances {P : BudgetPoint} {V : Support n} {F H : Config G n → ℂ} (h : P.Regular V F) (he : P.Regular V H)
    (o : Site n) {x y : ℝ} (hx : P.supBounds o V F x) (hy : P.supBounds o V H y) : P.supBounds o V (F+H) (x+y) := by
  refine ⟨add_nonneg hx.1 hy.1,fun U hU l hl ha => ?_⟩
  rw [Crest.sum_at l hl U (into _ _ (h.smooth U hU)) (into _ _ (he.smooth U hU))]
  exact (norm_add_le ..).trans (add_le_add (hx.2 _ hU l hl ha) (hy.2 _ hU l hl ha))
end YM.Multi.Puff
