import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Moment

/-!
# Price derivative of a joint Gaussian moment

Real directions on the *actual* covariance from differentiating a common
replica representation. Keep ordered derivatives even when two endpoints of
the new edge hit the same occurrence. No derivative of an inverse or estimate
on the row derivative of a square root uniform across volumes needed here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.GCC
open MeasureTheory Filter Function Set Finset
open YM.Multi.Vacuum.Gauss Probe Quadratic
open scoped Topology BigOperators

variable {I J V : Type} [Fintype I] [Fintype J] [DecidableEq V] [DecidableEq I]
namespace Moment
variable (s : Finset V) (q : Rows V I J) (v : Probes V I)

omit [Fintype I] in
lemma values_mark (i : V) (hi : i∈s) (a : I) (x) : values s q (marked v i a) x=
    values (s.erase i) q v x * hit (v i) a (mapRows (q i) x) := by
  unfold values
  rw [← prod_erase_mul _ _ hi]
  simp only [marked, update_self]
  congr 1
  exact prod_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]

/-- derivative through position i (in all coordinates) in marked form. -/
lemma at_position (i : V) (hi : i∈s) (x : Row J) (y : Row I) :
    values (s.erase i) q v x • (fderiv ℝ (v i) (mapRows (q i) x) y)=
      ∑ a,y a • values s q (marked v i a) x := by
  rw [all_axes,Finset.smul_sum]; refine sum_congr rfl fun a _ => ?_
  rw [values_mark s q v i hi, Complex.real_smul, Complex.real_smul]; change _*_=_; ring

lemma dvalues (h : ∀ i∈s,Differentiable ℝ (v i)) : Differentiable ℝ (values s q v) ∧
    ∀ x u : Row J,fderiv ℝ (values s q v) x u = ∑ i∈s,∑ a, crossed (q i a) u • values s q (marked v i a) x := by
  let E (i : V) (x : Row J) := v i (mapRows (q i) x)
  have hd (x : Row J) i (hi : i∈s) : HasFDerivAt (E i) _ x :=
    (h i hi (mapRows (q i) x)).hasFDerivAt.comp x (hasFDerivAt_pi.mpr fun a => crossed_deriv (q i a) _)
  have hg (x : Row J) : HasFDerivAt (values s q v) _ x := HasFDerivAt.finsetProd (hd x)
  refine ⟨fun x => (hg x).differentiableAt,fun x u => ?_⟩
  rw [(hg x).fderiv,_root_.sum_apply]; refine sum_congr rfl fun i hi => ?_
  rw [smul_apply,ContinuousLinearMap.comp_apply]
  change values (s.erase i) q v x • (fderiv ℝ (v i) (mapRows (q i) x) _) = _
  rw [at_position s q v i hi]; refine sum_congr rfl fun a _ => ?_
  rw [ContinuousLinearMap.pi_apply,plane_read]

lemma moves (q p : ℝ → Rows V I J) (h : ∀ i∈s,Differentiable ℝ (v i)) (x : Row J) (y : ℝ)
    (hp : ∀ i∈s, ∀ a,HasDerivAt (fun t => q t i a) (p y i a) y) :
    HasDerivAt (fun t => values s (q t) v x)
      (∑ i∈s,∑ a,crossed (p y i a) x • values s (q y) (marked v i a) x) y := by
  let E i := fun t => v i (mapRows (q t i) x)
  have he (i : V) (hi : i∈s) : HasDerivAt (fun t => mapRows (q t i) x)
      (mapRows (p y i) x) y := by
    apply hasDerivAt_pi.mpr; intro a
    unfold mapRows
    simp_rw [crossed_comm _ x]
    rw [← plane_read]
    have h1 := HasFDerivAt.comp_hasDerivAt (l:=crossed x) y
      (f:=fun t => q t i a) (crossed_deriv x (q y i a)) (hp i hi a)
    exact h1
  have hg := HasDerivAt.finsetProd (f:=E)
    (fun i hi => (h i hi _).hasFDerivAt.comp_hasDerivAt y (he i hi))
  convert! hg using 1
  · ext t; simp [E,values,Finset.prod_apply]
  exact sum_congr rfl fun i hi => (at_position s (q y) v i hi x (mapRows (p y i) x)).symm

section
variable {s q v}
variable {T : Finset V} {w : V → Row I} {H : V → ℕ → ℝ}
omit [DecidableEq V] in
private lemma integral_linear {n : ℕ} (h : Valid T n v w H) (hs : s ⊆ T) (hx : base q T w) (y : Row J) :
    Integrable (fun x => crossed y x • values s q v x) (standard J) := by
  let L := fun _ : Unit => q
  let U := Set.univ (α:=Unit)
  have hr := values_growth U L hs h
  have hg : Growth U (fun _ _ => 0) (fun _ => crossed y) := Growth.lines (squares_nn y) (q:=fun _ => y) (fun _ _ => le_rfl)
  apply (hg.real_mul hr).integrable (works U L hs (fun _ _ => hx)) (Set.mem_univ ())
  exact (crossed_cont _).smul (values_continuous (fun i hi => h.read i (hs hi)) q)

/-- Stein's identity with polynomial or mildly exponential costs for the
marks. Includes the integrability statement to enable further summation. -/
theorem linear_pay (h : Valid T 1 v w H) (hs : s ⊆ T) (hx : base q T w) (y : Row J) :
    Integrable (fun x => crossed y x • values s q v x) (standard J) ∧
    (∫ x,crossed y x • values s q v x ∂standard J) = ∑ i∈s,∑ a,crossed (q i a) y • total s q (marked v i a) := by
  have he := integral_linear h hs hx y
  have hi i (_hi : i∈s) (a : I) : Integrable (fun x => crossed (q i a) y • values s q (marked v i a) x) (standard J) :=
    (revenues hx (h.mark i a) hs).1.smul (crossed (q i a) y)
  obtain ⟨hf,hg⟩ := dvalues s q v (fun i hi => h.look zero_lt_one i (hs hi))
  refine ⟨he,?_⟩
  rw [weighted_stein y _ hf (revenues hx h hs).1 he ?_]
  · simp_rw [hg]; rw [integral_finsetSum]; rotate_left
    · exact fun i hh => integrable_finsetSum _ (fun j _ => hi i hh j)
    refine sum_congr rfl fun i hh => ?_
    rw [integral_finsetSum _ (fun j _ => hi i hh j)]; simp_rw [integral_smul]; rfl
  simp_rw [hg]
  exact integrable_finsetSum _ (fun i hh => integrable_finsetSum _ (fun j _ => hi i hh j))

/-- Differentiate a submoment at a point. The additional test on actual
row velocities `p` here is only finite-volume LOCAL, not supposed to be a
uniform physical bill. The formula retains it paired exactly, so for
example at interpolated covariance only prices the original unvaried
entries. -/
theorem supported_flow (s : Finset V) (q p : ℝ → Rows V I J) (h : Valid T 2 v w H) (hs : s⊆T) (y : ℝ) (S : Set ℝ) (hy : S ∈ 𝓝 y)
    (hq : ∀ t∈S,base (q t) T w) (hh : ∀ i∈s, ∀ a,∃ C, 0≤C ∧ ∀ t∈S,squares (p t i a) ≤ C)
    (he : ∀ t∈S,∀ i∈s,∀ a,HasDerivAt (fun t => q t i a) (p t i a) t) :
    HasDerivAt (fun t => total s (q t) v)
      (∑ i∈s,∑ a,∑ j∈s,∑ b,crossed (q y j b) (p y i a) • total s (q y) (marked (marked v i a) j b)) y := by
  let d (t : ℝ) (i : V) (a : I) x := crossed (p t i a) x • values s (q t) (marked v i a) x
  let g (t : ℝ) x := ∑ i∈s, ∑ a, d t i a x
  let U t := sumCharge s (q t) w
  have hx : y∈S := mem_of_mem_nhds hy
  have ht (i : V) (a : I) := h.mark i a
  have hd : Growth S U g := by
    apply Growth.sum_many; intro i hi
    apply Growth.sum_many; intro a _
    obtain ⟨C,hC,h₀⟩ := hh i hi a
    exact (Growth.lines hC h₀).real_mul (values_growth S q hs (ht i a))
  have hc : Continuous (g y) := continuous_finsetSum _ fun i hi => continuous_finsetSum _ fun a _ =>
    (crossed_cont (p y i a)).smul (values_continuous (fun j hj => (ht i a).read j (hs hj)) _)
  have h' := Growth.derivative (values_growth S q hs h) hd (works S q hs hq) hy (fun t _ =>
    values_continuous (fun i hi => h.read i (hs hi)) _) hc (fun x t h₀ => moves s v q p
      (fun i hi => h.look (by norm_num) i (hs hi)) x t (he t h₀))
  have hl i a := linear_pay (ht i a) hs (hq y hx) (p y i a)
  have hh : (∫ x,g y x ∂standard J) = ∑ i∈s,∑ a,∑ j∈s,∑ b,crossed (q y j b) (p y i a) • total s (q y) (marked (marked v i a) j b) := by
    unfold g; rw [integral_finsetSum]; rotate_left
    · exact fun i _ => integrable_finsetSum _ fun a _ => (hl i a).1
    apply sum_congr rfl; intro i _
    rw [integral_finsetSum _ (fun a _ => (hl i a).1)]
    exact sum_congr rfl fun a _ => (hl i a).2
  rw [← hh]; exact h'
end
end Moment
end YM.Primitives.GCC
