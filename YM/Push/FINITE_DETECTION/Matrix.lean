import YM.Next.EXTRACTION.Detector

/-!
# Finite matrix comparison on the varying image 

Exact cutoffs first. Weak columns need not be in the chosen complement: *apply* the
step projection to them using the upper-equation smallness on tests. An upper count
on the finite cutoff image (e.g. from injective coordinates for equation cylinders)
is also needed. Only keep one sufficiently deep weak stage `k` at a given weight when
constructing `Detector`. Bounds paying the columns and changes of testing rows can
blow up with `k`; lower bound eventually uniform in the ordered `(N,p)` tails, **not**
uniform in `k`, unless these costs are. No continuum rank hypothesis.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.FiniteDetection
open Function Filter Dash Extraction Next.Extract Set
open scoped Topology BigOperators

section Matrices
variable {V E Z T : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup Z] [NormedSpace ℂ Z]

lemma injective_bound (F : V →L[ℂ] Z) [FiniteDimensional ℂ Z] (h : Injective F) :
    ∃ a : ℝ, 0 < a ∧ ∀ x, a * ‖x‖ ≤ ‖F x‖ := by
  let L := LinearMap.toContinuousLinearMap F.toLinearMap.leftInverse
  have he x : L (F x) = x := LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr h) x
  refine ⟨1/(1+‖L‖),by positivity,fun x => ?_⟩
  rw [one_div, mul_comm, ← div_eq_mul_inv]
  refine (div_le_iff₀ (by positivity)).mpr ?_
  have hw := L.le_opNorm (F x)
  rw [he] at hw; nlinarith [norm_nonneg (F x)]

lemma loses (F L : V →L[ℂ] Z) (x : V) : ‖F x‖ ≤ ‖F-L‖ * ‖x‖ + ‖L x‖ := calc
  _ = ‖(F-L) x + L x‖ := by rw [sub_apply, sub_add_cancel]
  _ ≤ _ := (norm_add_le ..).trans (by gcongr; exact (F-L).le_opNorm x)

lemma test_projected (P : E →L[ℂ] E) (X : V →L[ℂ] E) (A : E →L[ℂ] Z) (H : V →L[ℂ] Z)
    {a δ : ℝ} (hH : ∀ x, a * ‖x‖ ≤ ‖H x‖)
    (he : ‖H - A.comp X‖ + ‖(A - A.comp P).comp X‖ ≤ δ) (x : V) :
    (a-δ) * ‖x‖ ≤ ‖A (P (X x))‖ := by
  have h := (hH x).trans (loses H (A.comp X) x)
  have h' := loses (A.comp X) ((A.comp P).comp X) x
  rw [show A.comp X - (A.comp P).comp X = (A - A.comp P).comp X by ext; rfl] at h'
  simp only [ContinuousLinearMap.comp_apply] at h h'
  nlinarith [mul_le_mul_of_nonneg_right he (norm_nonneg x)]

variable [FiniteDimensional ℂ E]

/-- Exact moving-image estimate; no topology on cutoffs or weak scales needed. -/
theorem matrix_bound (P : E →L[ℂ] E) (X : V →L[ℂ] E) (A : E →L[ℂ] Z) (H : V →L[ℂ] Z)
    (hr : Module.finrank ℂ (LinearMap.range P.toLinearMap) ≤ Module.finrank ℂ V)
    {a δ D : ℝ} (hH : ∀ x, a * ‖x‖ ≤ ‖H x‖)
    (hd : δ < a) (he : ‖H - A.comp X‖ + ‖(A - A.comp P).comp X‖ ≤ δ)
    (hD : 0 < D) (hX : ‖P.comp X‖ ≤ D) :
    Injective (P.comp X) ∧ LinearMap.range (P.comp X).toLinearMap = LinearMap.range P.toLinearMap ∧
    ∀ v ∈ LinearMap.range P.toLinearMap, ((a-δ) / D) * ‖v‖ ≤ ‖A v‖ := by
  let Q := P.comp X
  have hl (x : V) : (a-δ) * ‖x‖ ≤ ‖A (Q x)‖ := test_projected P X A H hH he x
  have hi : Injective Q := by
    intro x y h
    have hx := hl (x-y)
    rw [map_sub, h, sub_self, map_zero, norm_zero] at hx
    by_contra hne
    exact (mul_pos (sub_pos.mpr hd) (norm_pos_iff.mpr (sub_ne_zero.mpr hne))).not_ge hx
  have hh : LinearMap.range Q.toLinearMap = LinearMap.range P.toLinearMap :=
    Submodule.eq_of_le_of_finrank_le (LinearMap.range_comp_le_range X.toLinearMap P.toLinearMap)
      (by rwa [LinearMap.finrank_range_of_inj (f := Q.toLinearMap) hi])
  refine ⟨hi,hh,fun v hv => ?_⟩
  obtain ⟨w,rfl⟩ := (hh.symm ▸ hv : v ∈ LinearMap.range Q.toLinearMap)
  change (a-δ)/D * ‖Q w‖ ≤ ‖A (Q w)‖
  have hb := (Q.le_opNorm w).trans (mul_le_mul_of_nonneg_right hX (norm_nonneg w))
  calc
    _ ≤ (a-δ)/D * (D*‖w‖) := by gcongr
    _ = (a-δ)*‖w‖ := by field_simp
    _ ≤ _ := hl w
end Matrices

variable {G : Gauge} {C : Family G} {f : Order} {b : Presentation C} {d : ℕ}
    {ι V Z : Type*} [Fintype ι]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup Z] [NormedSpace ℂ Z]

/-- Stack actual normalized mesh scans in the sup norm. -/
def observe (s : ι → Shot C.book) (d : ℕ) (u : ℕ×ℕ) : C.label d →L[ℂ] ι → ℂ :=
  ContinuousLinearMap.pi fun i => snapshots (s i) d u

open Classical in
lemma observe_paid (s : ι → Shot C.book) (d : ℕ) (u) (v : C.label d) :
    ‖observe s d u v‖ ≤ ∑ i ∈ Finset.univ.image s, ‖snapshots i d u v‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  exact fun i => Finset.single_le_sum (f := fun j => ‖snapshots j d u v‖) (by intros; positivity)
    (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)

open Classical in
/-- One explicit finite family. `B` permits bounded combinations at this cutoff
(e.g. expanding a varying normalized spectator in a reference basis). -/
theorem one_cut (s : ι → Shot C.book) (u : ℕ×ℕ) (X : V →L[ℂ] C.label d)
    (B : (ι → ℂ) →L[ℂ] Z) (H : V →L[ℂ] Z)
    (hr : Module.finrank ℂ (LinearMap.range (b.step d u).toLinearMap) ≤ Module.finrank ℂ V)
    {a δ L D : ℝ} (hH : ∀ x, a * ‖x‖ ≤ ‖H x‖) (hd : δ < a)
    (he : let A := B.comp (observe s d u)
          ‖H - A.comp X‖ + ‖(A - A.comp (b.step d u)).comp X‖ ≤ δ)
    (hL : 0 < L) (hB : ‖B‖ ≤ L) (hD : 0 < D) (hX : ‖(b.step d u).comp X‖ ≤ D) :
    ∀ v : C.label d, b.step d u v = v → (a-δ)/D/L * ‖v‖ ≤ ∑ i ∈ Finset.univ.image s, ‖snapshots i d u v‖ := by
  let O := observe s d u
  have hl := (matrix_bound (b.step d u) X (B.comp O) H hr hH hd he hD hX).2.2
  intro v hv
  rw [div_mul_eq_mul_div, div_le_iff₀ hL, mul_comm _ L]
  exact (hl v ⟨v,hv⟩).trans ((B.le_opNorm _).trans (by
    apply mul_le_mul hB (observe_paid s d u v) (norm_nonneg _) hL.le))

/-- Exactly the vanishing estimate needed from the cutoff equations here. No
shortage, projector limit, or smooth hierarchy. -/
def Silent (b : Presentation C) (f : Order) (d : ℕ) := ∀ (i : Shot C.book) (x : C.label d),
  Tendsto (fun u => snapshots i d u (x - b.step d u x)) f.fuse (𝓝 0)

lemma observation_null (hs : Silent b f d) (s : ι → Shot C.book) :
    Tendsto (fun u => observe s d u - (observe s d u).comp (b.step d u)) f.fuse (𝓝 0) := by
  let A u := observe s d u - (observe s d u).comp (b.step d u)
  have ht (x : C.label d) : Tendsto (fun u => A u x) f.fuse (𝓝 0) := tendsto_pi_nhds.mpr fun i => by
    change Tendsto (fun u => snapshots (s i) d u x - snapshots (s i) d u (b.step d u x)) _ (𝓝 0)
    simpa only [map_sub] using hs (s i) x
  exact fit_plane (fun u => (A u).toLinearMap) 0 ht

/-- Bounded on ordered tails (sup / operator norm). -/
def cost {E : Type*} [Norm E] (f : Order) (X : ℕ×ℕ → E) := ∃ D : ℝ, 0 < D ∧ ∀ᶠ u in f.fuse, ‖X u‖ ≤ D

/-- Outer weak stage then fused cutoff tails. (Not mesh convergence
at every individual period; those quantifiers used separately at extraction.) -/
abbrev deep (f : Order) := (atTop : Filter ℕ).curry f.fuse

open Classical in
/-- Perturbation on all sufficiently accurate weak stages: the stage can then
be FROZEN for actual finite physical detection. No assumption of spanning by
normalized columns. All estimates/test comparisons on the given family only.
Use `Silent` to project after, not before asking for weak comparison. -/
theorem eventual_bound [FiniteDimensional ℂ Z]
    (H : V →L[ℂ] Z) (s : ℕ → ι → Shot C.book)
    (B : ℕ → ℕ×ℕ → (ι → ℂ) →L[ℂ] Z) (X : ℕ → ℕ×ℕ → V →L[ℂ] C.label d)
    (h : Injective H) (hr : ∀ᶠ u in f.fuse, Module.finrank ℂ (LinearMap.range (b.step d u).toLinearMap) ≤ Module.finrank ℂ V)
    (hs : Silent b f d) (hp : cost f (b.step d))
    (hB : ∀ᶠ k in atTop, cost f (B k)) (hX : ∀ᶠ k in atTop, cost f (X k))
    (he : Tendsto (fun (t : ℕ×(ℕ×ℕ)) => ((B t.1 t.2).comp (observe (s t.1) d t.2)).comp (X t.1 t.2)) (deep f) (𝓝 H)) :
    ∀ᶠ k in atTop, ∃ c : ℝ, 0 < c ∧ ∀ᶠ u in f.fuse,
      ∀ v : C.label d, b.step d u v = v → c * ‖v‖ ≤ ∑ i ∈ Finset.univ.image (s k), ‖snapshots i d u v‖ := by
  obtain ⟨a,ha,hH⟩ := injective_bound H h
  obtain ⟨P,hP,hp⟩ := hp
  have he' := ((tendsto_const_nhds (x := H)).sub he).norm.eventually (ge_mem_nhds
    (show ‖H-H‖ < a/3 by simpa using (by linarith : 0 < a/3)))
  -- split only the desired nested eventuality (not arbitrary product tails)
  filter_upwards [hB,hX, Filter.eventually_curry_iff.mp he'] with k hB hX he
  obtain ⟨L,hL,hB⟩ := hB; obtain ⟨D,hD,hX⟩ := hX
  refine ⟨(a-(a/3+a/3))/(P*D)/L,by exact div_pos (div_pos (by linarith) (mul_pos hP hD)) hL, ?_⟩
  let O := observe (s k) d
  have hw := (observation_null hs (s k)).norm.eventually (ge_mem_nhds
    (show ‖(0 : C.label d →L[ℂ] ι → ℂ)‖ < a/3/D/L by rw [norm_zero]; positivity))
  filter_upwards [hr, hp, hB, hX, he, hw] with u hr hp hB hX he hw
  apply one_cut (s k) u (X k u) (B k u) H hr hH (by linarith : a/3+a/3<a) ?_ hL hB (mul_pos hP hD) ?_
  · let A := (B k u).comp (O u)
    let J := O u - (O u).comp (b.step d u)
    have he' : ‖H - A.comp (X k u)‖ ≤ a/3 := he
    have hw' : ‖J‖ ≤ a/3/D/L := hw
    refine add_le_add he' ?_
    change ‖(A-A.comp (b.step d u)).comp (X k u)‖ ≤ a/3
    rw [show A - A.comp (b.step d u) = (B k u).comp J by ext x; apply (map_sub (B k u) _ _).symm]
    calc
      _ ≤ (‖B k u‖ * ‖J‖) * ‖X k u‖ := ((ContinuousLinearMap.opNorm_comp_le ..)).trans
        (by gcongr; exact ContinuousLinearMap.opNorm_comp_le ..)
      _ ≤ (L * (a/3/D/L)) * D := by gcongr
      _ = a/3 := by field_simp
  exact (ContinuousLinearMap.opNorm_comp_le ..).trans (by gcongr)

open Classical in
lemma detector_freeze (s : ι → Shot C.book) {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ u in f.fuse, ∀ v : C.label d, b.step d u v = v → c * ‖v‖ ≤ ∑ i ∈ Finset.univ.image s, ‖snapshots i d u v‖) : Detector b f d :=
  ⟨Finset.univ.image s, c, hc, (f.fused _).mp h⟩
end YM.Push.FiniteDetection
