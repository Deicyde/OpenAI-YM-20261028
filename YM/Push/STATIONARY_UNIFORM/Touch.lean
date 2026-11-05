import YM.Push.STATIONARY_UNIFORM.Slope

/-!
# Localization calculus for the real implicit jets

Take the envelopes for all derivatives in the unapplied score, compose
multilinear entries through *located* maps of potentially good jets. The
extensive F cannot be composed by the simple sup estimate so work via
derivatives of individual components. These are tools to pay distances
once along the implicit tree (for fixed derivative order). All sums over
physical sites really on full torus. Uses summability over intermediate
indices with multiplicities, not uniform entries alone.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Filter Function Set Metric Lattice Matrix
open scoped Topology ContDiff BigOperators Classical

variable {ι τ E : Type} [Fintype ι] [Fintype τ] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : Side} {p : Positions ι} {q : Positions τ} {l : ι → Site n} {m : τ → Site n}

lemma multi_expansion {k} (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => Positions ι) ℝ) (z : Fin k → Positions ι) :
    T z = ∑ j : Fin k → ι, (∏ i, z i (j i))*T (fun i => bolt (j i)) := by
  have h := T.map_sum (α:=fun _ => ι) (fun i t => z i t • bolt t)
  simp_rw [combine] at h
  apply h.trans; exact Finset.sum_congr rfl (fun i _ => T.map_smul_univ (fun j => z j (i j)) _)

lemma entry_projects (f : Positions ι → Positions τ) (hf : ContDiffAt ℝ ω f p) {k} (i) (q : Fin k → ι) :
    entry (fun x => f x i) p q = entry f p q i := by
  let L := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : τ => ℝ) i
  unfold entry; rw [show (fun x => f x i) = L ∘ f from rfl,L.iteratedFDeriv_comp_left hf le_top]; rfl

def glaze {k : ℕ} (l : ι → Site n) (x : Site n) (p : Fin k → ι) (a : ℝ) := Real.exp (-a*spanSites l x p)

omit [Fintype ι] in
lemma glaze_prod {k : ℕ} (l : ι → Site n) (x : Site n) (p : Fin k → ι) (a : ℝ) :
    glaze l x p a = ∏ i, Decay a x (l (p i)) := by simp_rw [glaze, Decay,spanSites,Nat.cast_sum, Finset.mul_sum, Real.exp_sum]

-- Transfer a decay at y *from* all the slots to a cost relative x. -
omit [Fintype ι] in
lemma path_price {k N : ℕ} (h : k≤N) {a r : ℝ} (ha : 0<a) (hr : 0<r) (l : ι → Site n) (x y : Site n) (p : Fin k → ι) :
    Decay a x y * glaze l y p r ≤ Decay (a/2) x y * glaze l x p (min r (weaker N a)) := by
  unfold Decay glaze; rw [← Real.exp_add,← Real.exp_add,Real.exp_le_exp]
  have he : spanSites l x p ≤ (N+1)*separation x y+spanSites l y p := calc
    _ ≤ ∑ i, (separation x y+separation y (l (p i))) := Finset.sum_le_sum fun i _ => separation_triangle ..
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]; unfold spanSites
      apply Nat.add_le_add_right _ _; simp only [Finset.sum_const,nsmul_eq_mul, Finset.card_univ,Fintype.card_fin]; exact Nat.mul_le_mul_right (separation x y) (show k ≤ N+1 by omega)
  let γ := min r (weaker N a)
  have hg : 0 ≤ γ := le_min hr.le (by unfold weaker; positivity)
  have hs : γ * spanSites l x p ≤ a/2 * separation x y + r * spanSites l y p := calc
    _ ≤ γ * ((N+1:ℝ)*separation x y+(spanSites l y p:ℝ)) := mul_le_mul_of_nonneg_left (by exact_mod_cast he) hg
    _ ≤ weaker N a*((N+1:ℝ)*separation x y) + r * (spanSites l y p:ℝ) := by
      rw [mul_add]; exact add_le_add (mul_le_mul_of_nonneg_right (min_le_right ..) (by positivity)) (mul_le_mul_of_nonneg_right (min_le_left ..) (by positivity))
    _ = _ := by unfold weaker; field_simp
  unfold γ at hs; linarith

omit [Fintype ι] in
lemma glaze_mono {k : ℕ} (l : ι → Site n) (x : Site n) (p : Fin k → ι) {a r : ℝ} (hr : r ≤ a) :
    glaze l x p a ≤ glaze l x p r := Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg hr) (by positivity))

omit [Fintype ι] in
lemma glaze_partition {k : ℕ} (s : OrderedFinpartition k) (l : ι → Site n) (x : Site n) (p : Fin k → ι) (a : ℝ) :
    ∏ i : Fin s.length, glaze l x (p ∘ s.emb i) a = glaze l x p a := by
  simp_rw [glaze, ← Real.exp_sum, ← Finset.mul_sum,← Nat.cast_sum]; rw [show (∑ i, spanSites l x (p ∘ s.emb i)) = _ from s.sum_sigma_eq_sum (fun i => separation x (l (p i)))]
  rfl

variable {f : Positions ι → Positions τ} {g : Positions τ → ℝ} {a r C D : ℝ} {K N k : ℕ}

lemma wire_cost (q : Fin k → ι) (s : OrderedFinpartition k) (hk : k ≤ N) (ha : 0<a) (hr : 0<r) (hp : 0 ≤ C)
    (hD : 0 ≤ D) (u : Site n) (hm : Multiplicity m K)
    (hh : Beacon m a k g u (f p) C)
    (h : ∀ i j, ‖(entry f p (q ∘ s.emb i) : Positions τ) j‖ ≤ D*glaze l (m j) (q ∘ s.emb i) r) :
    ‖((ftaylorSeries ℝ g (f p)).compAlongOrderedFinpartition (ftaylorSeries ℝ f p) s) (fun j => bolt (q j))‖ ≤
      C*(D*((K:ℝ)*countCost (a/2)))^s.length * glaze l u q (min r (weaker N a)) := by
  let Z i := entry f p (q ∘ s.emb i)
  let c := min r (weaker N a); let L := Fin s.length; let M : ℝ := (K:ℝ)*countCost (a/2)
  let H (i : L) (j : τ) := D*glaze l (m j) (q ∘ s.emb i) r
  let Q (s : L → τ) := (∏ i, Z i (s i))*entry g (f p) s
  have hs (i : L) (j) : ‖Z i j‖ ≤ H i j := h i j
  let F (i : L) (j : τ) := H i j*Decay a u (m j)
  have hF i j : 0 ≤ F i j := mul_nonneg (mul_nonneg hD (Real.exp_pos _).le) (decay_pos ..).le
  have he j : ‖Q j‖ ≤ C*∏ i, F i (j i) := by
    unfold Q; rw [norm_mul,norm_prod]; apply le_trans (mul_le_mul (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hs i _))
      (hh _ s.length_le _) (norm_nonneg _) (Finset.prod_nonneg (fun i _ => mul_nonneg hD (Real.exp_pos _).le)))
    rw [show Real.exp (-a*↑(spanSites m u j))= _ from glaze_prod m u j a]; unfold F H; simp_rw [Finset.prod_mul_distrib]; exact le_of_eq (by ring)
  have hx i : ∑ j, F i j ≤ D*M*glaze l u (q ∘ s.emb i) c := by
    let P := q ∘ s.emb i
    calc
      _ ≤ ∑ j, Decay (a/2) u (m j) * (D*glaze l u P c) := Finset.sum_le_sum fun j _ => by
        have hv := mul_le_mul_of_nonneg_left (path_price ((s.partSize_le i).trans hk) ha hr l u (m j) P) hD
        change D*glaze l (m j) P r * _ ≤ _
        unfold c
        linarith only [hv]
      _ = (∑ j, Decay (a/2) u (m j))*(D*glaze l u P c) := by rw [Finset.sum_mul]
      _ ≤ M*(D*glaze l u P c) := mul_le_mul_of_nonneg_right (hm.count m (half_pos ha) u) (mul_nonneg hD (Real.exp_pos _).le)
      _ = _ := by unfold P; ring
  have ha : ((ftaylorSeries ℝ g (f p)).compAlongOrderedFinpartition (ftaylorSeries ℝ f p) s) (fun j => bolt (q j)) = ∑ j, Q j := multi_expansion (iteratedFDeriv ℝ s.length g (f p)) Z
  rw [ha]
  apply le_trans ((norm_sum_le ..).trans (Finset.sum_le_sum (fun i _ => he i)))
  rw [← Finset.mul_sum, ← Fintype.prod_sum]
  apply le_trans (mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _ => Finset.sum_nonneg (fun j _ => hF i j)) (fun i _ => hx i)) hp)
  apply le_of_eq; rw [Finset.prod_mul_distrib, glaze_partition, Finset.prod_const,Finset.card_univ]; simp only [M,L,c, mul_assoc,Fintype.card_fin]

lemma scatter_derivative (f : Positions ι → ℝ) (hf : ContDiffAt ℝ ω f p) (h : Scatter l a N f p C) (u : ι) (hk : k < N) :
    Beacon l a k (fun x => fderiv ℝ f x (bolt u)) (l u) p C := by
  intro i hi q
  let s : Fin (i+1) → ι := Fin.snoc (α:=fun _ : Fin (i+1) => ι) q u
  have he : entry (fun x => fderiv ℝ f x (bolt u)) p q = entry f p s := by
    let L := ContinuousLinearMap.apply ℝ ℝ (bolt u)
    unfold entry
    rw [show (fun x => fderiv ℝ f x (bolt u)) = L ∘ fderiv ℝ f from rfl,
      L.iteratedFDeriv_comp_left (hf.fderiv_right (m:=ω) (by simp)) le_top,iteratedFDeriv_succ_apply_right]
    have hv : s (Fin.last i)=u := by unfold s; rw [Fin.snoc_last]
    change (iteratedFDeriv ℝ i (fderiv ℝ f) p _ ) (bolt u) = _
    simp only [hv]
    congr 2
    funext j; simp [s,Fin.init]
  rw [he]; simpa [s,spanSites,Fin.sum_univ_castSucc] using h (i+1) (by omega) s (Fin.last i)
end YM.Push.Uniform
