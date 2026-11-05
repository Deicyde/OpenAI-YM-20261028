import YM.Next.WARD_BIN.Linear

/-!
# Reading the linear equation maps with a finite set of samples

Equality on triangular inputs. Shrinking-grid argument ONLY to inferring linear span in
finite dimensions, not a continuum-limit assertion. This includes the position slopes of
face averages needed with both signs in `sample_net`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Set Filter Lattice Wilson RG Labels Source Source.Drops MeasureTheory
open Work.G03
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {j d : ℕ}

private def averaged {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : E4 → E) (p q : E4)
    (x : E4) (t : ℝ) := ∫ s : ℝ in 0..1, ∫ r : ℝ in 0..1, v (x+(t*s) • p + (t*r) • q)

/-- Slope version for coalescing positions under shrinking scale. -/
private theorem avg_slope {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (v : E4 → E) (hv : ContDiff ℝ 1 v) (p q V x : E4) (X : ℝ → E4)
    (h : Tendsto X (𝓝[>] (0:ℝ)) (𝓝 x)) :
    Tendsto (fun t : ℝ => t⁻¹ • (averaged v p q (X t + t • V) t - averaged v p q (X t) t))
      (𝓝[>] 0) (𝓝 (fderiv ℝ v x V)) := by
  let F := fun y : E4 × ℝ => ∫ s : ℝ in 0..1, ∫ r : ℝ in 0..1, ∫ u : ℝ in 0..1,
    fderiv ℝ v (y.1 + (y.2*s) • p + (y.2*r) • q + (y.2*u) • V) V
  have hc : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by decide)
  have ht : Continuous F := by
    unfold F
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'; unfold uncurry
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'; unfold uncurry
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    fun_prop
  have hz : F (x,0) = fderiv ℝ v x V := by simp [F]
  have hu (a : E4) (t : ℝ) : averaged v p q (a+t • V) t - averaged v p q a t = t • F (a,t) := by
    let z (a : E4) (s r : ℝ) := a + (t*s) • p + (t*r) • q
    have hh (k : E4) (u : ℝ) : HasDerivAt (fun r : ℝ => v (k + (t*r) • V))
        (t • (fderiv ℝ v (k + (t*u) • V) V)) u := by
      have ha : HasDerivAt (fun r : ℝ => k + (t*r) • V) (t • V) u := by
        simpa only [one_mul,mul_one,nsmul_eq_mul,zero_add] using! (hasDerivAt_const u k).add (((hasDerivAt_id' u).const_mul t).smul_const V)
      simpa only [map_smul] using! ((hv.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt u ha)
    have hc₀ (a : E4) (s : ℝ) : IntervalIntegrable (fun r => v (z a s r)) volume 0 1 :=
      (hv.continuous.comp (show Continuous (z a s) by unfold z; fun_prop)).intervalIntegrable _ _
    have hc₁ (a : E4) : Continuous (fun s : ℝ => ∫ r : ℝ in 0..1, v (z a s r)) := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'; unfold uncurry z
      fun_prop (disch := aesop)
    unfold averaged
    rw [← intervalIntegral.integral_sub ((hc₁ (a+t • V)).intervalIntegrable _ _) ((hc₁ a).intervalIntegrable _ _)]
    unfold F; rw [← intervalIntegral.integral_smul]; apply intervalIntegral.integral_congr; intro s _
    change (∫ r : ℝ in 0..1, v (z (a+t • V) s r)) - (∫ r : ℝ in 0..1,v (z a s r)) = _
    rw [← intervalIntegral.integral_sub (hc₀ (a+t • V) s) (hc₀ a s)]; dsimp only; rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr; intro r _
    change _ - _ = t • ∫ u : ℝ in 0..1, fderiv ℝ v (z a s r + (t*u) • V) V
    rw [← intervalIntegral.integral_smul, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hh (z a s r) u)]
    · rw [mul_zero,mul_one,zero_smul,add_zero, show z (a+t • V) s r = z a s r + t • V by unfold z; abel]
    apply Continuous.intervalIntegrable; fun_prop
  have hp : Tendsto (fun t : ℝ => F (X t,t)) (𝓝[>] 0) (𝓝 (F (x,0))) :=
    ht.continuousAt.tendsto.comp (h.prodMk_nhds (tendsto_id.mono_left nhdsWithin_le_nhds))
  rw [hz] at hp; refine hp.congr' ?_
  filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t ht
  rw [hu _ _, inv_smul_smul₀]
  exact ne_of_gt ht

private theorem grad_good (k i : Axis) (A : Taylor G d) : ContDiff ℝ 1 (Maxwell.grad k (A.value i)) := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  apply Maxwell.grad_smooth (n:= (1:WithTop ℕ∞)+1) k (Tensor.diag_smooth _ _|>.contDiffAt) le_rfl

lemma net_slope (X : ℝ → E4) (x : E4) (hx : Tendsto X (𝓝[>] (0:ℝ)) (𝓝 x))
    (A : Taylor G j) (a b v : Axis) :
    Tendsto (fun t : ℝ => t⁻¹ • (net A a b (X t-t • basis v) t-net A a b (X t) t))
      (𝓝[>] 0) (𝓝 (-Maxwell.grad v (Tensor.diagonal (Maxwell.takeCurl A a b)) x)) := by
  have h (a b v : Axis) : Tendsto (fun t : ℝ => t⁻¹ • (meanPartial A a b (X t-t • basis v) t-meanPartial A a b (X t) t))
      (𝓝[>] 0) (𝓝 (-(fderiv ℝ (Maxwell.grad a (A.value b)) x (basis v)))) := by
    change Tendsto (fun t : ℝ => t⁻¹ • (averaged _ (basis b) (basis a) (X t-t • basis v) t-averaged _ _ _ _ t)) _ _
    simpa only [smul_neg, ← sub_eq_add_neg, map_neg] using!
      avg_slope (Maxwell.grad a (A.value b)) (grad_good a b A) (basis b) (basis a) (-basis v) x X hx
  have he := (h a b v).sub (h b a v)
  have hp (t : ℝ) : t⁻¹ • (net A a b (X t-t • basis v) t-net A a b (X t) t) = _ := calc
    _ = t⁻¹ • ((meanPartial A a b (X t - t • basis v) t-meanPartial A a b (X t) t) -
        (meanPartial A b a (X t-t • basis v) t-meanPartial A b a (X t) t)) := by unfold net; congr 1; abel
    _ = _ := smul_sub ..
  have hl : -(fderiv ℝ (Maxwell.grad a (A.value b)) x (basis v)) -
      -(fderiv ℝ (Maxwell.grad b (A.value a)) x (basis v)) =
      - Maxwell.grad v (Tensor.diagonal (Maxwell.takeCurl A a b)) x := by
    rw [Maxwell.takeCurl_diag]
    change _ = -(fderiv ℝ (Maxwell.grad a (A.value b) - Maxwell.grad b (A.value a)) x (basis v))
    rw [fderiv_sub ((grad_good a b A).differentiable (by decide) _)
      ((grad_good b a A).differentiable (by decide) _), sub_apply]
    abel
  simp_rw [hp]; rw [hl] at he; exact he


open Maxwell

/-- Read the divergence of the linear-curvature jet (undivided sign). -/
def curlDiv (i : Axis) (x : E4) : Taylor G j →L[ℝ] G.Color :=
  LinearMap.toContinuousLinearMap {
    toFun A := ∑ a : Axis, grad a (Tensor.diagonal (takeCurl A a i)) x
    map_add' A B := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro a _
      have he : takeCurl (A+B)=takeCurl A + takeCurl B := congr_arg Subtype.val (Maxwell.potential.map_add A B)
      rw [he]
      change fderiv ℝ (Tensor.diagonal (takeCurl A a i)+Tensor.diagonal (takeCurl B a i)) x _ = _
      rw [fderiv_add ((Tensor.diag_smooth _ ∞).differentiable (by simp) _)
        ((Tensor.diag_smooth _ ∞).differentiable (by simp) _)]; rfl
    map_smul' r A := by
      rw [RingHom.id_apply, Finset.smul_sum]; apply Finset.sum_congr rfl; intro a _
      have he : takeCurl (r • A)=r • takeCurl A := congr_arg Subtype.val (map_smul Maxwell.potential r A)
      rw [he]
      change fderiv ℝ (r • Tensor.diagonal (takeCurl A a i)) x _ = _
      rw [fderiv_const_smul ((Tensor.diag_smooth _ ∞).differentiable (by simp) _)]
      rfl }

lemma curl_div_at (i : Axis) (x : E4) (A : Taylor G j) : curlDiv i x A =
    ∑ a : Axis with a≠i, grad a (Tensor.diagonal (takeCurl A a i)) x := by
  change ∑ a : Axis, grad a (Tensor.diagonal (takeCurl A a i)) x = _; symm
  apply Finset.sum_subset (Finset.filter_subset ..)
  intro a _ ht; simp only [Finset.mem_filter,Finset.mem_univ,true_and,ne_eq,not_not] at ht
  subst a; simp only [takeCurl,sub_self,smul_zero]
  change fderiv ℝ (fun _ : E4 => (0:G.Color)) x _ = _; simp

/-- Slots controlled in the exact evaluation identity: ignore higher degrees
of the tested inputs until after choosing these coefficients. -/
def through (G : Gauge) (d j : ℕ) : Submodule ℝ (Snap G d) where
  carrier := {A | ∀ k : Fin (d-1), j < k.val → A k=0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {a b} (h : ∀ k : Fin (d-1), j < k.val → a k=0) (h' : ∀ k : Fin (d-1), j < k.val → b k=0) k hk => by
    change (a+b) k=0; rw [Pi.add_apply,h _ hk,h' _ hk,add_zero]
  smul_mem' := fun r A (h : ∀ k : Fin (d-1), j < k.val → A k=0) k hk => by change (r • A) k=0; rw [Pi.smul_apply,h k hk,smul_zero]

private lemma cast_prev (x : Cover) (k : Axis) : castPos (x-step k) = castPos x - basis k := by
  have he := castPos_step (x-step k) k
  rw [sub_add_cancel] at he; exact eq_sub_of_add_eq he.symm

-- value limit, including `j=0`, then span in a finite-dimensional map space
private lemma div_limit (H : Hol G) (k : Fin (d-1)) (v : Axis) (x : E4) (A : through G d k.val) :
    Tendsto (fun t : ℝ => t^(k.val-1) • linearSample H (index t x,v) (A : Snap G d))
      (𝓝[>] 0) (𝓝 (-curlDiv v x ((A : Snap G d) k))) := by
  let Z : ℝ → Cover := fun t => index t x
  let X : ℝ → E4 := fun t => t • castPos (Z t)
  have hX : Tendsto X (𝓝[>] 0) (𝓝 x) := shrink_grid x
  let f (j : ℕ) (l : Axis) (y : Cover) := net (expand d (A : Snap G d) j) l v (castPos (y-step l)) 1 -
    net (expand d (A : Snap G d) j) l v (castPos y) 1
  have ht (a : Axis) {j : ℕ} (h : j ≤ k.val) :
      Tendsto (fun t : ℝ => t^(k.val-1) • f j a (Z t)) (𝓝[>] 0)
        (𝓝 ((0:ℝ)^(k.val-j) • (- grad a (Tensor.diagonal (takeCurl (expand d (A : Snap G d) j) a v)) x))) := by
    -- pay also k=0: t^(k-j)/t times degree t^j,
    -- adjustment k=0 has zero net on that term.
    let B := expand d (A : Snap G d) j
    have hP := net_slope X x hX B a v a
    have hs := (Filter.Tendsto.pow (l:=𝓝[>] (0:ℝ))
      (show Tendsto (fun x : ℝ => x) _ (𝓝 (0:ℝ)) from tendsto_id.mono_left nhdsWithin_le_nhds) (k.val-j)).smul hP
    refine hs.congr' ?_; filter_upwards [self_mem_nhdsWithin (s:=Ioi (0:ℝ))] with t ht
    have hr : 0 < t := ht; let y := Z t
    rw [show X t - t • basis a = t • castPos (y-step a) by rw [cast_prev,smul_sub], show X t = t • castPos y from rfl,
      scale_net, scale_net, ← smul_sub, smul_smul,smul_smul,mul_assoc]
    change (t^(k.val-j) * (t⁻¹ * t^j)) • f j a y = _
    by_cases hh : k.val=0
    · have hj : j=0 := by omega
      subst j
      have he (p : E4) : net B a v p 1 = net B a v 0 0 := by simpa using (scale_net (k:=0) B a v p 0).symm
      unfold f
      change _ • (net B a v _ 1-net B a v _ 1) = _ • (net B a v _ 1-net B a v _ 1)
      rw [he,he,sub_self,smul_zero]; simp
    have he : t^(k.val-j)*(t⁻¹*t^j) = t^(k.val-1) := by
      apply mul_left_cancel₀ hr.ne'
      calc
        _ = t^(k.val-j) * t^j := by ring_nf; field_simp
        _ = t^k.val := by rw [← pow_add, Nat.sub_add_cancel h]
        _ = t * t^(k.val-1) := by rw [← pow_succ',Nat.sub_add_cancel (Nat.pos_of_ne_zero hh)]
    rw [he]
  have hh (p : Cover) : ∑ m∈ Finset.range (k.val+1), ∑ l : Axis with l≠v, f m l p = linearSample H (p,v) (A : Snap G d) := by
    rw [sample_net]
    apply Finset.sum_subset (Finset.range_mono (show k.val+1 ≤ d-1 from k.isLt))
    intro m hm he; rw [Finset.mem_range] at hm he
    have hg : expand d (A : Snap G d) m=0 := dif_pos hm |>.trans (A.property _ (by change k.val<m; omega))
    unfold f; rw [hg]; simp only [net_zero,sub_self,Finset.sum_const_zero]
  simp_rw [← hh,Finset.smul_sum]
  have HE := tendsto_finsetSum (M:=G.Color) (s:=Finset.range (k.val+1)) fun m hm =>
    tendsto_finsetSum (s:=Finset.univ.filter fun l => l≠v) fun a _ => ht a (Nat.le_of_lt_succ (Finset.mem_range.mp hm))
  have hr : ∑ m∈Finset.range (k.val+1), ∑ j : Axis with j≠v, (0:ℝ)^(k.val-m) •
      (-grad j (Tensor.diagonal (takeCurl (expand d (A : Snap G d) m) j v)) x) = -curlDiv v x ((A : Snap G d) k) := by
    rw [Finset.sum_range_succ, Finset.sum_eq_zero]
    · simp only [Nat.sub_self,pow_zero,one_smul,zero_add,Finset.sum_neg_distrib,curl_div_at,
        expand,dif_pos k.isLt]
    intro i hi; simp_rw [zero_pow (Nat.sub_ne_zero_of_lt (Finset.mem_range.mp hi)),zero_smul]
    exact Finset.sum_const_zero
  rw [hr] at HE; exact HE

private lemma fetch {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (Q : E →L[ℝ] F) (Y : Cover → E →L[ℝ] F) (f : ℝ → Cover) (f' : ℝ → ℝ)
    (hp : ∀ i,Tendsto (fun t : ℝ => f' t • Y (f t) i) (𝓝[>] (0:ℝ)) (𝓝 (Q i))) :
    ∃ (c : Cover →₀ ℝ), ∀ i,(∑ y∈c.support,c y • Y y i)=Q i := by
  let U := fun t : ℝ => f' t • Y (f t)
  -- operator topology is enough (finite dimensional)
  have h (X : E →L[ℝ] F) (f : ℝ → E →L[ℝ] F) (p : Filter ℝ)
      (he : ∀ i,Tendsto (fun t : ℝ => f t i) p (𝓝 (X i))) : Tendsto f p (𝓝 X) := by
    let b := Module.finBasis ℝ E
    let L := LinearMap.toContinuousLinearMap.toLinearMap.comp (b.constr ℝ (M':=F)).toLinearMap
    have hv (X : E →L[ℝ] F) : L (fun i => X (b i))=X := by
      apply ContinuousLinearMap.coe_injective; exact b.ext fun i => b.constr_basis ..
    have hL := L.continuous_of_finiteDimensional.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr
      (show ∀ i,Tendsto (fun t : ℝ => (fun j : Fin (Module.finrank ℝ E) => f t (b j)) i) p
        (𝓝 ((fun j : Fin (Module.finrank ℝ E) => X (b j)) i)) from fun i => he _))
    convert hL using 1
    · funext i; exact (hv _).symm
    rw [hv]
  have hQ : Q ∈ Submodule.span ℝ (Set.range Y) := by
    apply (Submodule.span ℝ (Set.range Y)).closed_of_finiteDimensional.mem_of_tendsto (h Q U _ hp)
    exact Eventually.of_forall fun t => (Submodule.span ℝ (Set.range Y)).smul_mem (f' t)
      (Submodule.subset_span (show Y (f t)∈Set.range Y from ⟨_,rfl⟩))
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hQ
  refine ⟨c,fun x => ?_⟩
  have he := DFunLike.congr_fun hc x
  unfold Finsupp.sum at he; rw [sum_apply] at he; exact he

private lemma fetchSub {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (S : Submodule ℝ E)
    (Q : E →L[ℝ] F) (Y : Cover → E →L[ℝ] F) (f : ℝ → Cover) (f' : ℝ → ℝ)
    (hp : ∀ i : S,Tendsto (fun t : ℝ => f' t • Y (f t) (i : E)) (𝓝[>] (0:ℝ)) (𝓝 (Q i))) :
    ∃ (c : Cover →₀ ℝ), ∀ x∈S,(∑ y∈c.support,c y • Y y x)=Q x := by
  obtain ⟨c,hc⟩ := fetch (Q.comp S.subtypeL) (fun y => (Y y).comp S.subtypeL) f f' hp
  exact ⟨c,fun A hA => hc (⟨A,hA⟩:S)⟩

/-- Real sample reads exact on lower slots. The fact that projection is triangular
in this sense is used at *fixed factor degree*, not claiming vanishing of all lower
engineering degrees in the fully nonlinear lattice gauge equation. -/
theorem samples (H : Hol G) (k : Fin (d-1)) (v : Axis) (x : E4) :
    ∃ (c : Cover →₀ ℝ), ∀ A ∈ through G d k.val,
      (∑ y ∈ c.support, c y • linearSample H (y,v) A) = -curlDiv v x (A k) := by
  exact fetchSub (through G d k.val)
    ((-curlDiv (G:=G) (j:=k.val) v x).comp (ContinuousLinearMap.proj (φ:=fun j : Fin (d-1) => Taylor G j.val) k))
    (fun y => linearSample H (y,v)) (fun t => index t x) (fun t => t^(k.val-1)) (div_limit H k v x)
end YM.WardBin
