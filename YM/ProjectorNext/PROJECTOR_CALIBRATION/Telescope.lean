import YM.ProjectorNext.PROJECTOR_CALIBRATION.Filters

/-! # Telescope a polarized label along one equation leg -/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration.Cross
open Function Filter Tensor
open scoped Topology BigOperators ContDiff
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {l : ℕ}
variable (B : Tensor.T X ℂ l) (Q : Module.End ℝ X)

/-- Arguments for one crossed leg; further legs read Qx (constraints
satisfied), previous positions have x restored. -/
def field (x : X) (i : Fin l) : Fin l → X := fun j => if j < i then x else Q x

def cell (x : X) (i : Fin l) (y : X) := update (field Q x i) i y

def mix (x : X) : X →L[ℝ] ℂ := ∑ i, B.toContinuousLinearMap (field Q x i) i

theorem mixSum (x y : X) : mix B Q x y = ∑ i : Fin l, B (cell Q x i y) := by
  unfold mix; rw [sum_apply]; rfl

private def ramp (x : X) (n : ℕ) (j : Fin l) := if j.val<n then x else Q x

/-- Include l=0. The equation hypothesis will ensure the sum of shell
evaluations =0 instead of hiding a possible degree-zero input. -/
theorem restore (x : X) : mix B Q x (x-Q x)=Tensor.diagonal B x - Tensor.diagonal B (Q x) := by
  have hh (i : Fin l) : B (cell Q x i (x-Q x)) = B (ramp Q x (l:=l) (i.val+1)) - B (ramp Q x i.val) := by
    unfold cell; rw [B.map_update_sub]
    congr 2
    · funext j; by_cases h : j=i
      · subst j; simp [ramp]
      rw [update_of_ne h]
      have he : j < i ↔ j.val < i.val+1 := by change j.val < i.val ↔ _; have hx : j.val ≠ i.val := fun he => h (Fin.ext he); omega
      simp [field,he,ramp]
    funext j; by_cases h : j=i
    · subst j; simp [ramp]
    rw [update_of_ne h]; rfl
  rw [mixSum]
  simp_rw [hh]
  let f (i : ℕ) := B (ramp Q x i)
  rw [Fin.sum_univ_eq_sum_range (fun i => f (i+1)-f i) l,Finset.sum_range_sub]
  unfold f ramp Tensor.diagonal
  simp

def rate (x dx : X) (y : X) := ∑ i : Fin l, ∑ j ∈ Finset.univ.erase i, B (update (cell Q x i y) j (field Q dx i j))

variable [FiniteDimensional ℝ X]

lemma cell_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → X} {n : WithTop ℕ∞}
    {a : E} (i : Fin l) (h : ContDiffAt ℝ n f a) (hd : ContDiffAt ℝ n g a) :
    ContDiffAt ℝ n (fun z => cell Q (f z) i (g z)) a := by
  apply contDiffAt_pi.mpr; intro j
  unfold cell field; by_cases hh : j=i
  · subst j; simp; exact hd
  simp_rw [update_of_ne hh]; split
  · exact h
  exact (LinearMap.toContinuousLinearMap Q).contDiff.contDiffAt.comp a h

lemma mix_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → X} {n : WithTop ℕ∞}
    {a : E} (h : ContDiffAt ℝ n f a) (hd : ContDiffAt ℝ n g a) :
    ContDiffAt ℝ n (fun z => mix B Q (f z) (g z)) a := by
  simp_rw [mixSum]
  exact ContDiffAt.sum fun i _ => B.contDiffAt.comp a (cell_smooth Q i h hd)

lemma rate_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f df g : E → X} {n : WithTop ℕ∞}
    {a : E} (h : ContDiffAt ℝ n f a) (he : ContDiffAt ℝ n df a) (hd : ContDiffAt ℝ n g a) :
    ContDiffAt ℝ n (fun z => rate B Q (f z) (df z) (g z)) a := by
  unfold rate
  refine ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => B.contDiffAt.comp (f:=fun z => update (cell Q (f z) i (g z)) j (field Q (df z) i j)) a ?_
  refine contDiffAt_pi.mpr fun k => ?_
  by_cases hk : k=j
  · subst k; simp_rw [update_self]; unfold field; split
    · exact he
    exact (LinearMap.toContinuousLinearMap Q).contDiff.contDiffAt.comp a he
  simp_rw [update_of_ne hk]
  exact contDiffAt_pi.mp (cell_smooth Q i h hd) k

lemma cell_deriv {f g : ℝ → X} {x y : X} {a : ℝ} (i : Fin l) (h : HasDerivAt f x a) (hd : HasDerivAt g y a) :
    HasDerivAt (fun z => cell Q (f z) i (g z)) (cell Q x i y) a := by
  apply hasDerivAt_pi.mpr; intro j
  by_cases hi : j=i
  · subst j; simpa [cell] using hd
  simp_rw [cell,update_of_ne hi]; unfold field; split
  · exact h
  exact (LinearMap.toContinuousLinearMap Q).hasFDerivAt.comp_hasDerivAt a h

/-- Full derivative needed when making the Haar divergence; don't drop the
contribution from y (used for differentiation of the transport). -/
lemma mix_deriv {f g : ℝ → X} {x y : X} {a : ℝ} (h : HasDerivAt f x a) (hd : HasDerivAt g y a) :
    HasDerivAt (fun z => mix B Q (f z) (g z)) (rate B Q (f a) x (g a) + mix B Q (f a) y) a := by
  unfold rate
  simp_rw [mixSum, ← Finset.sum_add_distrib]
  refine HasDerivAt.fun_sum fun i _ => ?_
  apply ((B.hasFDerivAt (cell Q (f a) i (g a))).comp_hasDerivAt a (cell_deriv Q i h hd)).congr_deriv
  rw [ContinuousMultilinearMap.linearDeriv_apply,← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    simp [cell,update_of_ne (Finset.ne_of_mem_erase hj)]
  simp [cell]

omit [FiniteDimensional ℝ X] in
lemma scaled_cell (T : Module.End ℝ X) (he : ∀ x, Q (T x)=T (Q x)) (x y : X) (i : Fin l) :
    cell Q (T x) i (T y) = fun j => T (cell Q x i y j) := by
  ext k; unfold cell; by_cases hk : k=i
  · subst k; simp
  simp_rw [update_of_ne hk]; unfold field; split_ifs; rfl; rw [he]

omit [FiniteDimensional ℝ X] in
lemma scaled_mix (T : Module.End ℝ X) (t : ℝ) (h : ∀ x : Fin l → X, B (fun i => T (x i)) = t • B x)
    (he : ∀ x, Q (T x)=T (Q x)) (x y : X) :
    mix B Q (T x) (T y)=t • mix B Q x y := by
  simp_rw [mixSum,scaled_cell Q T he,h,Finset.smul_sum]

omit [FiniteDimensional ℝ X] in
lemma mix_degree (x y : X) (θ : ℝ) : mix B Q (θ • x) y=θ^(l-1) • mix B Q x y := by
  simp_rw [mixSum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  let u (j : Fin l) := if j=i then (1:ℝ) else θ
  have he : cell Q (θ • x) i y = u • cell Q x i y := by
    ext j; unfold cell; by_cases hh : j=i
    · subst j; simp [u]
    rw [update_of_ne hh,Pi.smul_apply',update_of_ne hh]
    unfold field; split_ifs <;> simp [u,hh]
  have hu : ∏ j,u j=θ^(l-1) := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    simp only [u,↓reduceIte,mul_one]
    rw [Finset.prod_congr rfl (g:=fun _ => θ) (fun j hj => if_neg (Finset.ne_of_mem_erase hj))]; simp
  rw [he,← hu]; exact B.map_smul_univ u _

omit [FiniteDimensional ℝ X] in
lemma rate_degree (x dx y : X) (θ : ℝ) : rate B Q (θ • x) dx y=θ^(l-2) • rate B Q x dx y := by
  unfold rate; simp_rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  have hi := Finset.ne_of_mem_erase hj
  let u (k : Fin l) := if k=j then (1:ℝ) else if k=i then 1 else θ
  have he : update (cell Q (θ • x) i y) j (field Q dx i j) = u • update (cell Q x i y) j (field Q dx i j) := by
    ext k; by_cases hk : k=j
    · subst k; simp [u]
    rw [update_of_ne hk, Pi.smul_apply',update_of_ne hk]
    by_cases hl : k=i
    · subst k; simp [cell,u,hk]
    simp_rw [cell, update_of_ne hl]; unfold field; split_ifs <;> simp [u,hk,hl]
  have hb : i ∈ Finset.univ.erase j := Finset.mem_erase_of_ne_of_mem hi.symm (Finset.mem_univ i)
  have hu : ∏ k,u k=θ^(l-2) := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j),← Finset.prod_erase_mul _ _ hb]
    simp only [u,if_neg hi.symm, ↓reduceIte,mul_one]
    rw [Finset.prod_congr rfl (g:=fun _ => θ) (fun k hk => by
      have hk' := Finset.mem_of_mem_erase hk; simp [Finset.ne_of_mem_erase hk',Finset.ne_of_mem_erase hk])]
    simp [Finset.card_erase_of_mem hb, Nat.sub_sub]
  rw [he,← hu]; exact B.map_smul_univ u _
end YM.ProjectorNext.Calibration.Cross
