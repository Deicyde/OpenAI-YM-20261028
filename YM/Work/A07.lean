import YM.Bid.Angular

/-!
# A07: transfer of internal Ward kernel detection

At a fixed degree cap, work on the fixed finite-dimensional **real** vector space
of `Winds` on the comparator side. Use its erasure hypothesis (not the
polar-vector test `cuts`) to choose a finite family of separating rows there.
On this same vector space we can run approximating rows with the S-kernels at
rescaled, still separated points. Jet convergence at *order zero* suffices
for eventual injectivity. Only then test on the unknown, k-dependent pulled-back
defect.

This is conditional on free erasure, aligned weak comparison, etc.; no
construction of `MaxwellData` or `ActLaw` here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.A07

open Org Table Climb Ward Set Function Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius

/-- Finite rows still separate. Does not assume nonzero dimension or
nonempty testing family. -/
theorem finite_rows {I E F : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [AddCommGroup F] [Module ℝ F]
    (f : I → E →ₗ[ℝ] F) (h : ∀ x : E, (∀ i, f i x = 0) → x = 0) :
    ∃ s : Finset I, Injective (LinearMap.pi (fun i : s => f i.1)) := by
  classical
  let K (s : Finset I) := ⨅ i : s, LinearMap.ker (f i.1)
  have ex : ∃ n : ℕ, ∃ s : Finset I, Module.finrank ℝ (K s) = n := ⟨_, ∅, rfl⟩
  obtain ⟨s, hs⟩ := Nat.find_spec ex
  refine ⟨s, LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_)⟩
  intro x hx
  have hmem : x ∈ K s := (Submodule.mem_iInf _).mpr fun j =>
    LinearMap.mem_ker.mpr (congr_fun hx j)
  refine h x fun i => ?_
  -- Inserting any further row leaves the intersection equal.
  have le : K (insert i s) ≤ K s := le_iInf fun j =>
    iInf_le_of_le (⟨j.1, Finset.mem_insert_of_mem j.2⟩ : (insert i s : Finset I)) le_rfl
  have he : K (insert i s) = K s := Submodule.eq_of_le_of_finrank_le le
    (hs ▸ Nat.find_min' ex (show ∃ s', Module.finrank ℝ (K s') = Module.finrank ℝ (K (insert i s)) from
      ⟨_, rfl⟩))
  rw [← he] at hmem
  exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hmem
    (⟨i, Finset.mem_insert_self ..⟩ : (insert i s : Finset I)))

/-- Full rank of approximating finite-dimensional systems, using convergence
on fixed inputs. No topology needed on E. -/
theorem eventually_injective {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℕ → E →ₗ[ℝ] F) (g : E →ₗ[ℝ] F) (hg : Injective g)
    (h : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (g x))) :
    ∀ᶠ k in atTop, Injective (f k) := by
  let B := Module.finBasis ℝ E
  have hl := B.linearIndependent.map' g (LinearMap.ker_eq_bot.mpr hg)
  have ht : Tendsto (fun k => f k ∘ B) atTop (𝓝 (g ∘ B)) :=
    tendsto_pi_nhds.mpr (fun i => h (B i))
  filter_upwards [ht.eventually hl.eventually] with k hk
  have hd := Submodule.range_ker_disjoint (show LinearIndependent ℝ (f k ∘ B) from hk)
  rw [B.span_eq] at hd
  exact LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun x hx =>
    Submodule.disjoint_def.mp hd _ (Submodule.mem_top) (LinearMap.mem_ker.mpr hx))

variable {G : Gauge} {L : Register G} {S : Table L}

section Param

/-- Package exactly the `Winds` restrictions as a *real* submodule. -/
def internal (H : S.RealSpin) (P : DiffPlan S) (d : ℕ) : Submodule ℝ (Two S d) where
  carrier := {T | Winds H P d T}
  add_mem' {x y} (hx : Winds H P d x) (hy : Winds H P d y) := by
    refine ⟨fun g hg u v z => ?_, fun u v z => ?_, fun u v => ?_, fun u => ?_,
      fun k h u v z => ?_⟩
    · simp only [LinearMap.add_apply, map_add, hx.polar g hg, hy.polar g hg]
    · simp only [LinearMap.add_apply, map_add, hx.real, hy.real]
    · simp only [LinearMap.add_apply, hx.unit, hy.unit, add_zero]
    · simp only [LinearMap.add_apply, hx.alt, hy.alt, add_zero]
    · exact (LinearMap.range _).add_mem (hx.rises k h u v z) (hy.rises k h u v z)
  zero_mem' := by
    exact ⟨by intros; simp, by intros; simp, by intros; simp, by intros; simp,
      by intros; simp⟩
  smul_mem' (c : ℝ) (x : Two S d) (hx : Winds H P d x) := by
    refine ⟨fun g hg u v z => ?_, fun u v z => ?_, fun u v => ?_, fun u => ?_,
      fun k h u v z => ?_⟩
    · change S.mirror H _ _ (c • _) = c • x (orients g u) _ _
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, hx.polar g hg]
    · change S.conj H _ (c • _) = c • x u v _
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smulₛₗ, hx.real]
      change (starRingEnd ℂ) ((c : ℝ) : ℂ) • _ = ((c : ℝ) : ℂ) • x u v _
      rw [Complex.conj_ofReal]
    · change c • x u v (S.unit d) = _
      simp [hx.unit]
    · change c • x u u = _
      simp [hx.alt]
    · change c • x u v _ ∈ LinearMap.range _
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      exact (LinearMap.range _).smul_mem _ (hx.rises k h u v z)

variable {d : ℕ}

/-- Transport both ways between free and actual internal map-shaped data. -/
def pushTwo (U : Spin.change S d) : Two (Bel L) d ≃ₗ[ℝ] Two S d := by
  let e : ((Bel L).Field d →ₗ[ℂ] (Bel L).Field d) ≃ₗ[ℂ] (S.Field d →ₗ[ℂ] S.Field d) :=
    LinearEquiv.arrowCongr U U
  let a : (Ortho.Skew →ₗ[ℝ] ((Bel L).Field d →ₗ[ℂ] (Bel L).Field d)) ≃ₗ[ℝ]
      (Ortho.Skew →ₗ[ℝ] (S.Field d →ₗ[ℂ] S.Field d)) :=
    LinearEquiv.arrowCongr (LinearEquiv.refl ℝ _) (e.restrictScalars ℝ)
  exact LinearEquiv.arrowCongr (LinearEquiv.refl ℝ _) a

theorem push_apply (U : Spin.change S d) (T : Two (Bel L) d) (u v : Ortho.Skew)
    (x : (Bel L).Field d) : pushTwo U T u v (U x) = U (T u v x) := by
  change U (T u v (U.symm (U x))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem pull_apply (U : Spin.change S d) (T : Two S d) (u v : Ortho.Skew)
    (x : (Bel L).Field d) : U ((pushTwo U).symm T u v x) = T u v (U x) := by
  rw [← push_apply, LinearEquiv.apply_symm_apply]

/-- `Align` protects the `Winds` side conditions, even for maps varying with k. -/
theorem pull_winds (X : Scaling S) {D : ℕ} {P : DiffPlan S} {Q : DiffPlan (Bel L)}
    {H a} (hX : X.Align P Q H a D) (hd : d ≤ D) (k : ℕ) (T : Two S d)
    (hT : Winds H P d T) : Winds a Q d ((pushTwo (X.U k d)).symm T) where
  polar g hg u v z := by
    apply (X.U k d).injective
    rw [(hX.Hsym k d hd).1, pull_apply, pull_apply, hT.polar g hg, (hX.Hsym k d hd).1]
  real u v z := by
    apply (X.U k d).injective
    rw [(hX.Hsym k d hd).2, pull_apply, pull_apply, (hX.Hsym k d hd).2, hT.real]
  unit u v := by
    apply (X.U k d).injective
    rw [pull_apply, hX.carries k d hd, hT.unit, map_zero]
  alt u := by
    apply LinearMap.ext
    intro z
    apply (X.U k d).injective
    rw [pull_apply, hT.alt]; simp
  rises c hc u v z := by
    obtain ⟨y, hy⟩ := hT.rises c hc u v (X.U k c z)
    obtain ⟨w, rfl⟩ := (X.U k c).surjective y
    refine ⟨w, (X.U k d).injective ?_⟩
    rwa [pull_apply, hX.incl k c d hc hd, hX.incl k c d hc hd]
end Param

-- Aid typeclass search through the nested maps (same additive structures).
local instance agInner (d : ℕ) : AddCommGroup (Ortho.Skew →ₗ[ℝ] (S.Field d →ₗ[ℂ] S.Field d)) :=
  inferInstance
local instance agTwo (d : ℕ) : AddCommGroup (Two S d) := inferInstance

theorem finiteDimensional_internal (H : S.RealSpin) (P : DiffPlan S) (d : ℕ) :
    FiniteDimensional ℝ (internal H P d) := by
  letI : FiniteDimensional ℝ (S.Field d →ₗ[ℂ] S.Field d) := Module.Finite.trans ℂ _
  infer_instance

section Rows

variable {d : ℕ}

/-- The row-sum in `erases`, as a real linear map. -/
def rowSum {m : ℕ} (x : Points m) (w : Fin m → S.Field d) (u v : Ortho.Skew) :
    Two S d →ₗ[ℝ] ℂ := by
  let obs : (S.Field d →ₗ[ℂ] S.Field d) →ₗ[ℂ] ℂ :=
    (observed w x d).comp LinearMap.toContinuousLinearMap.toLinearMap
  exact (obs.restrictScalars ℝ).comp ((LinearMap.applyₗ v).comp (LinearMap.applyₗ u))

theorem rowSum_eq {m : ℕ} (x : Points m) (w : Fin m → S.Field d) (u v : Ortho.Skew)
    (T : Two S d) : rowSum x w u v T =
      ∑ i, disc (update (Climb.column w) i ⟨d, T u v (w i)⟩) x :=
  observation w (LinearMap.toContinuousLinearMap (T u v)) x

/-- One test at a separated configuration. -/
structure CellRow (S : Table L) (d : ℕ) where
  m : ℕ
  x : Points m
  separated : x ∈ conf m
  w : Fin m → S.Field d
  u : Ortho.Skew
  v : Ortho.Skew

def CellRow.testRow (q : CellRow S d) : Two S d →ₗ[ℝ] ℂ :=
  rowSum q.x q.w q.u q.v

/-- Windows exhaust all separated points including tuples of length zero and one. -/
theorem eventually_window {m : ℕ} (x : Points m) (hx : x ∈ conf m) :
    ∀ᶠ R : ℝ in atTop, x ∈ Scaling.window R m := by
  have sp : ∀ᶠ R : ℝ in atTop, spaced R⁻¹ x := by
    unfold spaced
    refine Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
      Filter.eventually_all.mpr fun h => ?_
    have hp : 0 < cubedist (x i) (x j) := dist_pos.mpr fun e =>
      h ((show Injective x.ofLp from hx) ((WithLp.ofLp_injective 2) e))
    exact (eventually_ge_atTop _).mono fun _ he => inv_le_of_inv_le₀ hp he
  exact sp.and (eventually_ge_atTop ‖x‖)

/-- The approximating row, still a linear map on the *fixed free side*. -/
def actual (X : Scaling S) (k : ℕ) (q : CellRow (Bel L) d) : Two (Bel L) d →ₗ[ℝ] ℂ :=
  (rowSum (X.r k • q.x) ((X.U k d) ∘ q.w) q.u q.v).comp (pushTwo (X.U k d)).toLinearMap

theorem actual_eq (X : Scaling S) (k : ℕ) (q : CellRow (Bel L) d) (T : Two (Bel L) d) :
    actual X k q T = ∑ i, disc (X.pins k ∘ update (Climb.column q.w) i
      (⟨d, T q.u q.v (q.w i)⟩ : (Bel L).Tag)) (X.r k • q.x) := by
  change rowSum (X.r k • q.x) ((X.U k d) ∘ q.w) q.u q.v (pushTwo (X.U k d) T) = _
  rw [rowSum_eq]
  apply Finset.sum_congr rfl; intro i _
  congr 1
  funext j
  by_cases h : j = i
  · subst j
    simp only [comp_apply, update_self, push_apply]
    rfl
  · simp only [comp_apply, update_of_ne h]; rfl

/-- Zero-th order jet convergence for a fixed word. -/
theorem value_limit (X : Scaling S) {N m j : ℕ} {R : ℝ} (hb : X.jets N d j R)
    (hm : m ≤ N) (x : Points m) (hx : x ∈ Scaling.window R m)
    (w : Fin m → (Bel L).Tag) (hw : ∀ i, (w i).1 ≤ d) :
    Tendsto (fun k => disc (X.pins k ∘ w) (X.r k • x)) atTop (𝓝 (disc w x)) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  filter_upwards [hb m hm 0 (Nat.zero_le j) w hw (ε/2) (by positivity)] with k hk
  rw [dist_eq_norm]
  specialize hk x hx
  simp only [iteratedFDeriv_zero_eq_comp, comp_apply, ← map_sub, LinearIsometryEquiv.norm_map] at hk
  exact hk.trans_lt (half_lt_self hε)

/-- Pointwise convergence of each approximating row on the free map space.
Not applied to a k-dependent transformed argument. -/
theorem row_limit (X : Scaling S) (q : CellRow (Bel L) d) (T : Two (Bel L) d) {N j : ℕ} {R : ℝ}
    (hm : q.m ≤ N) (hx : q.x ∈ Scaling.window R q.m) (hb : X.jets N d j R) :
    Tendsto (fun k => actual X k q T) atTop (𝓝 (q.testRow T)) := by
  simp only [actual_eq, CellRow.testRow, rowSum_eq]
  refine tendsto_finsetSum _ fun i _ => value_limit X hb hm q.x hx _ fun l => ?_
  by_cases he : l = i
  · subst l; rw [update_self]
  · rw [update_of_ne he]
    exact le_rfl

end Rows

/-- Transfer from the free internal-map erasure input, on the same actual table
and aligned scalings. -/
theorem transfer (P : DiffPlan S) (R : Lighthouse L) (J : S.Stress)
    (H : S.RealSpin) (a : (Bel L).RealSpin) (A : ActLaw P R J H a)
    (hf : erases a R.W) : erases H P := by
  classical
  obtain ⟨n, hn⟩ := hf
  refine ⟨n, ?_⟩
  intro d hd
  let M : Submodule ℝ (Two (Bel L) d) := internal a R.W d
  letI : FiniteDimensional ℝ M := finiteDimensional_internal a R.W d
  let F (q : CellRow (Bel L) d) := q.testRow.comp M.subtype
  have detect (x : M) (hx : ∀ i, F i x = 0) : x = 0 := by
    apply Subtype.ext
    refine hn d hd _ x.2 ?_
    intro m p hp u v w
    rw [← rowSum_eq p w u v x.1]; exact hx ⟨m, p, hp, w, u, v⟩
  obtain ⟨s, hs⟩ := finite_rows F detect
  -- A single comparison system for this cap and all of these finitely many rows.
  let N := s.sup CellRow.m
  have hN (q : s) : q.1.m ≤ N := Finset.le_sup q.2
  have hw : ∀ᶠ B : ℝ in atTop, ∀ q : s, q.1.x ∈ Scaling.window B q.1.m :=
    Filter.eventually_all.mpr fun q => eventually_window _ q.1.separated
  obtain ⟨B, hB, hpts⟩ := ((eventually_ge_atTop 1).and hw).exists
  obtain ⟨X, hX⟩ := A.connects N d 0 B hB
  let f : ℕ → M →ₗ[ℝ] (s → ℂ) := fun k =>
    LinearMap.pi fun q : s => (actual X k q.1).comp M.subtype
  have he : ∀ᶠ k in atTop, Injective (f k) :=
    eventually_injective f _ hs fun x => tendsto_pi_nhds.mpr
      (fun q => row_limit X q.1 x.1 (hN q) (hpts q) hX.thick)
  obtain ⟨k, hk⟩ := he.exists
  intro T hT hz
  let y : M := ⟨(pushTwo (X.U k d)).symm T, pull_winds X hX.path (le_max_left d 4) k T hT⟩
  have hem : f k y = 0 := by
    funext q
    change rowSum (X.r k • q.1.x) ((X.U k d) ∘ q.1.w) q.1.u q.1.v
      (pushTwo (X.U k d) ((pushTwo (X.U k d)).symm T)) = 0
    rw [LinearEquiv.apply_symm_apply, rowSum_eq]
    refine hz _ _ ?_ _ _ _
    intro i j hij
    apply (show Injective q.1.x.ofLp from q.1.separated)
    exact smul_right_injective _ (X.positive k).ne' (show X.r k • q.1.x i = X.r k • q.1.x j from hij)
  have hy : (pushTwo (X.U k d)).symm T = 0 :=
    congr_arg Subtype.val (hk (hem.trans (map_zero (f k)).symm))
  exact (pushTwo (X.U k d)).symm.injective (hy.trans (map_zero _).symm)

theorem answer : YM.Bid.A07 := by
  intro G C S H V _ _ _ R J A
  exact transfer V R.T J H.spin R.hT.spin A R.frames

end YM.Work.A07
