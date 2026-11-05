import YM.Planned.ATOM_REGULAR_ESTIMATE.Faa
import YM.Planned.ATOM_REGULAR_ESTIMATE.Norm
import YM.Push.STATIONARY_UNIFORM.Beacons


/-! Link-log coordinates (not just *at* the identity). Relative moving charts
show the constants in replacing arbitrary finite-order polar tests by `B.supBounds`.
Use a support-limited chart for the short-support estimates; neither the estimator
nor its dimensions charge the possibly much larger ambient torus. -/

set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular
open Function Filter Set Metric Lattice Wilson RG Gauge Push
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G : Gauge} {n : Side}

section SmallCoordinate

def relay (G : Gauge) : G.Color × G.Color → G.Color := fun p =>
  G.plog (G.mat (G.lieExp p.1 * (G.lieExp p.2)⁻¹))
@[simp] lemma relay_diag (a : G.Color) : relay G (a,a) = 0 := by simp [relay]

lemma relay_diff (a : G.Color) : ContDiffAt ℝ ω (relay G) (a,a) := by
  unfold relay
  simp_rw [G.mat_mul, G.mat_inv]
  have h : ContDiffAt ℝ ω G.plog (G.mat (G.lieExp a)*star (G.mat (G.lieExp a))) := by
    rw [← G.mat_inv, ← G.mat_mul, mul_inv_cancel,G.mat_one]; exact G.plog_diff
  apply h.comp (a,a) (f:=fun p : G.Color × G.Color => G.mat (G.lieExp p.1) * star (G.mat (G.lieExp p.2)))
  exact (G.exp_jet.comp contDiff_fst).contDiffAt.mul
    ((((starL' ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.comp (G.exp_jet.comp contDiff_snd))).contDiffAt)

private lemma relay_price (G : Gauge) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a : G.Color, ‖a‖ ≤ 1 → Uniform.Allows n (relay G) (a,a) C := by
  obtain ⟨c,hc,h⟩ := Uniform.exists_allows ((isCompact_closedBall (0:G.Color) 1).image
    (show Continuous (fun p : G.Color => (p,p)) by fun_prop)) (forall_mem_image.mpr (fun a _ => relay_diff a)) n
  exact ⟨1+c,le_add_of_nonneg_right hc,fun a ha => (h _ ⟨a,by simpa, rfl⟩).mono (le_add_of_nonneg_left zero_le_one)⟩

def relayCost (G : Gauge) (n : ℕ) : ℝ := (relay_price G n).choose
lemma relay_one (G : Gauge) (n : ℕ) : 1 ≤ relayCost G n := (relay_price G n).choose_spec.1

/-- Holding the second input fixed. No power estimate uniform off the stated region. -/
lemma relay_allows (N : ℕ) {a : G.Color} (ha : ‖a‖ ≤ 1) :
    Uniform.Allows N (fun b : G.Color => relay G (b,a)) a (relayCost G N) := by
  let C := relayCost G N
  have h : Uniform.Allows N (relay G) (a,a) C := (relay_price G N).choose_spec.2 a ha
  let S (b : G.Color) := relay G (b,a)
  refine ⟨h.analytic.comp (f:=fun b => (b,a)) a (contDiffAt_id.prodMk contDiffAt_const),fun k hk => ?_⟩
  let T (z) := relay G ((a,a)+z)
  have ht : ContDiffAt ℝ k T 0 :=
    (show ContDiffAt ℝ k (relay G) ((a,a)+0) by rw [add_zero]; exact h.analytic.of_le le_top).comp (f:=fun z => (a,a)+z) 0 (contDiffAt_const.add contDiffAt_id)
  let L : G.Color →L[ℝ] G.Color × G.Color := ContinuousLinearMap.inl ℝ _ _
  have he : T ∘ L = (fun z => S (a+z)) := funext fun z => by simp [T,S,L]
  have hu := Next.Foundations.jets_linear L ht
  rw [he, iteratedFDeriv_comp_add_left, add_zero, show iteratedFDeriv ℝ k T 0 = iteratedFDeriv ℝ k (relay G) (a,a) by unfold T; rw [iteratedFDeriv_comp_add_left,add_zero]] at hu
  change ‖iteratedFDeriv ℝ k S a‖ ≤ C
  rw [hu]
  refine op_le_of_unit (zero_le_one.trans (relay_one ..)) fun v hv => ?_
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hS (i : Fin k) : ‖L (v i)‖ ≤ 1 := by simpa only [L,ContinuousLinearMap.inl_apply,Prod.norm_mk, norm_zero,max_le_iff] using And.intro (hv i) zero_le_one
  simpa using ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le (h.norm_le k hk) hS
end SmallCoordinate

def limitAmp (B : BudgetPoint) (o : Site n) (J : Finset (Link n)) : Directions G n →L[ℝ] Directions G n :=
  ContinuousLinearMap.pi fun e => if e∈J then weight B o e • ContinuousLinearMap.proj e else 0

@[simp] lemma limit_hit {B : BudgetPoint} {o : Site n} {J : Finset (Link n)} {e : Link n} (he : e∈J) (u : Directions G n) :
    limitAmp B o J u e = weight B o e • u e := by simp [limitAmp,he]
@[simp] lemma limit_miss {B : BudgetPoint} {o : Site n} {J : Finset (Link n)} {e : Link n} (he : e∉J) (u : Directions G n) :
    limitAmp B o J u e = 0 := by simp [limitAmp,he]

def bone (B : BudgetPoint) (o : Site n) (J : Finset (Link n)) (u : Directions G n) :=
  increment (1 : Config G n) (limitAmp B o J u)

section Shift
variable {B : BudgetPoint} {o : Site n} {J : Finset (Link n)}
variable {w : Directions G n}

def chain (B : BudgetPoint) (o : Site n) (J : Finset (Link n)) (w u : Directions G n) :=
    suppress B o (fun i => relay G (limitAmp B o J u i, limitAmp B o J w i))

@[simp] lemma chain_zero : chain B o J w w = 0 := by funext i; simp [chain]

lemma linked : bone B o J =ᶠ[𝓝 w] fun u => increment (bone B o J w) (amp B o (chain B o J w u)) := by
  let γ (u : Directions G n) (e : Link n) := G.lieExp (limitAmp B o J u e)
  have he : bone B o J = γ := funext fun u => funext fun e => by simp [bone, γ, increment]
  have hs (i : Link n) : Tendsto (fun u : Directions G n => γ u i*(γ w i)⁻¹) (𝓝 w) (𝓝 1) := by
    have h : Continuous (fun u : Directions G n => γ u i) := by unfold γ; fun_prop
    simpa using (h.mul_const ((γ w i)⁻¹)).tendsto w
  have ht : ∀ i : Link n, ∀ᶠ u in 𝓝 w, bone B o J u i = increment (bone B o J w) (amp B o (chain B o J w u)) i := by
    intro i; filter_upwards [(hs i).eventually G.plog_right] with u hu
    rw [he, increment, chain, amp_suppress]
    change _ = G.lieExp (G.plog (G.mat (γ u i*(γ w i)⁻¹))) * γ w i
    rw [hu, inv_mul_cancel_right]
  filter_upwards [eventually_all.mpr ht] with u hu
  exact funext hu

lemma chain_cost (N : ℕ)
    (hx : ∀ i∈J, ‖limitAmp B o J w i‖ ≤ 1) (hc : ∀ i∈J, weight B o i ≤ 1) :
    Uniform.Allows N (chain B o J w) w (relayCost G N) := by
  let C := relayCost G N
  have hC : 0 ≤ C := zero_le_one.trans (relay_one ..)
  refine Uniform.allows_pi hC fun i => ?_
  by_cases hi : i ∈ J
  · let a := weight B o i
    have ha : 0 < a := weight_pos ..
    let L : Directions G n →L[ℝ] G.Color := a • ContinuousLinearMap.proj i
    let q : G.Color := L w
    let f (b : G.Color) := relay G (b,q)
    have hF : Uniform.Allows N f q C := relay_allows N (by simpa only [limit_hit hi] using! hx i hi)
    have he : (fun u => chain B o J w u i) = a⁻¹ • (f ∘ (⇑L)) := by funext; simp only [chain,suppress_apply,limit_hit hi]; rfl
    rw [he]
    have hh : ContDiffAt ℝ ω (f ∘ (⇑L)) w := hF.analytic.comp (f:=L) w L.contDiff.contDiffAt
    refine ⟨hh.const_smul a⁻¹,fun k hk => ?_⟩
    by_cases h0 : k=0
    · subst k
      simpa [f,q] using hC
    have hD i' (v : Fin k → Directions G n) (he' : ‖v i'‖ ≤ 1) : ‖L (v i')‖ ≤ a := by
      rw [show L (v i') = a • v i' i from rfl,norm_smul_of_nonneg ha.le]
      exact mul_le_of_le_one_right ha.le ((norm_le_pi_norm (v i') i).trans he')
    rw [iteratedFDeriv_const_smul_apply (hh.of_le le_top), Uniform.iter_lin_at (L:=L) (show ContDiffAt ℝ k f q from hF.analytic.of_le le_top)]
    refine op_le_of_unit hC fun v hv => ?_
    rw [smul_apply, norm_smul_of_nonneg (inv_pos.mpr ha).le,ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have ht := ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le (hF.norm_le _ hk) (fun j => hD j v (hv j))
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at ht
    have hy : C*a^k ≤ C*a := mul_le_mul_of_nonneg_left (pow_le_of_le_one ha.le (hc i hi) h0) hC
    exact (mul_le_mul_of_nonneg_left (ht.trans hy) (inv_pos.mpr ha).le).trans_eq (by field_simp; rfl)
  have he (u : Directions G n) : chain B o J w u i = 0 := by simp [chain,hi]
  rw [funext he]
  exact Uniform.allows_const w (by rwa [norm_zero])

/-- Arity maximum for reexpanding. -/
def diagonals (n : ℕ) := ∑ i ∈ Finset.range (n+1), polarCost i
lemma diagonals_le {i n : ℕ} (h : i ≤ n) : polarCost i ≤ diagonals n :=
  Finset.single_le_sum (fun j _ => zero_le_one.trans (polar_one j)) (Finset.mem_range.mpr (by omega))
lemma diagonals_nonneg (n : ℕ) : 0 ≤ diagonals n := (zero_le_one.trans (polar_one 0)).trans (diagonals_le (Nat.zero_le n))

def baseCost (G : Gauge) (n : ℕ) := patterns n * diagonals n * (relayCost G n)^n
lemma baseCost_nonneg (G : Gauge) (n : ℕ) : 0 ≤ baseCost G n :=
  mul_nonneg (mul_nonneg (patterns_nonneg _) (diagonals_nonneg _)) (pow_nonneg (zero_le_one.trans (relay_one ..)) _)

/-- Bounds at an arbitrary log test within this stencil chart. -/
theorem base_bound {F : Config G n → ℂ} {Y : Support n} {c : ℝ} {k : ℕ}
    (hy : B.Regular Y F) (hf : B.supBounds o Y F c) (hk : k ≤ B.order)
    (hg : Healthy B.threshold Y (bone B o J w))
    (hx : ∀ i∈J, ‖limitAmp B o J w i‖ ≤ 1) (hc : ∀ i∈J, weight B o i ≤ 1) :
    ContDiffAt ℝ k (F ∘ bone B o J) w ∧
      ∀ i ≤ k, ‖iteratedFDeriv ℝ i (F ∘ bone B o J) w‖ ≤ baseCost G k * c := by
  let L := chain B o J w
  let H := charted F B o (bone B o J w)
  have ht := chain_cost k hx hc
  have hd : ContDiffAt ℝ k L w := ht.analytic.of_le le_top
  have he : ContDiffAt ℝ k H (L w) := by
    unfold L H
    rw [chain_zero]; exact (smooth_charted (hy.smooth _ hg) B o).of_le (Nat.cast_le.mpr hk)
  have hu : F ∘ bone B o J =ᶠ[𝓝 w] H ∘ L := linked.fun_comp F
  refine ⟨(he.comp w hd).congr_of_eventuallyEq hu, fun i hi => ?_⟩
  have h i (hi : i ≤ k) : ‖iteratedFDeriv ℝ i H (L w)‖ ≤ diagonals k*c := by
    unfold H L; rw [chain_zero]; exact (charted_bound hy hf hg (hi.trans hk)).trans
      (mul_le_mul_of_nonneg_right (diagonals_le hi) hf.1)
  rw [(hu.iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds]; exact (nest_bound hd he hi
    (mul_nonneg (diagonals_nonneg _) hf.1) (relay_one ..) (fun j _ hj => ht.norm_le j hj) h).trans_eq (by
      unfold baseCost; ring)
end Shift
end YM.Planned.AtomRegular
