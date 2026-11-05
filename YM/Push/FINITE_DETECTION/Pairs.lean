import YM.Push.FINITE_DETECTION.Matrix

/-!
# A weak pair-test implementation (E `klimA`, `WEbud`, `kwmap`)

Rescale a joint configuration-space bump by a *fixed physical radius per k*.
Use ordinary `Order.smears` on the TWO actual translated cylinders (not a fit in
an independently shifted hierarchy), both times on the **same** weak coordinates,
including their cutoff dependence. No cumulant subtraction in this comparison;
it needs convergence to the actual Maxwell moment (which includes the unit).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.FiniteDetection
open Function Filter Maxwell Dash Extraction Next.Extract Set
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {C : Family G} {f : Order} {b : Presentation C} {d : ℕ}

abbrev Standard (C : Family G) := Maxwell.freeTable C.labels
abbrev Model (C : Family G) (d : ℕ) := (Standard C).Field d
/-- Free ideal in reference coordinates (impose equations **before** testing).
Do not confuse with the Wilson finite-cutoff equation coordinate space. -/
abbrev Ideal (C : Family G) (d : ℕ) := LinearMap.ker (Maxwell.snap C.labels d)





variable {ι : Type*} [Fintype ι]
abbrev Coord (C : Family G) (d : ℕ) := (C.labels.level d).Index

def pairShot {L : Register G} (t : Test 2) {d : ℕ} (w : L.Ref d) : Shot L :=
  ⟨2,0,fun _ => ⟨d,w⟩,t⟩
/-- Actual finite family: all coordinate spectators at one rescaled two-point test. -/
def pairFamily (C : Family G) (d : ℕ) (t : Test 2) (j : Coord C d) : Shot C.book :=
  pairShot t (d := d) (Pi.single j 1)

def scanPair (C : Family G) (t : Test 2) (d : ℕ) (u : ℕ×ℕ) (v w : C.label d) : ℂ :=
  Order.smears C u.1 u.2 (fun j : Fin 2 => (⟨d,(![v,w] : Fin 2 → C.label d) j⟩ : C.book.Token)) t

lemma pair_mem {L : Register G} (t : Test 2) (v w : L.Ref d) : (pairShot (L := L) t (d := d) w).record (d := d) v =
    fun j : Fin 2 => (⟨d,(![v,w] : Fin 2 → L.Ref d) j⟩ : L.Token) := by
  funext i
  change Fin 2 at i
  fin_cases i <;> simp [pairShot,Shot.record]

lemma pair_snap (C : Family G) (t : Test 2) (d u) (v w : C.label d) :
    scanPair C t d u v w = snapshots (pairShot t (d := d) w) d u v := by
  change Order.smears C _ _ _ _ = Order.smears C _ _ _ t
  rw [pair_mem (d := d)]

def secondScan (C : Family G) (t : Test 2) {d} (v : C.label d) (u : ℕ×ℕ) : C.label d →L[ℂ] ℂ :=
  snapshots ⟨2,1,fun _ => ⟨d,v⟩,t⟩ d u

lemma second_scan (t : Test 2) (v w : C.label d) (u : ℕ×ℕ) : secondScan (d := d) C t v u w = scanPair C t d u v w := by
  apply congr_arg (fun x : Fin 2 → C.book.Token => Order.smears C u.1 u.2 x t)
  -- `record` at slot 1
  funext i
  fin_cases i <;> simp [Shot.record]

def pairMix (B : ι → C.label d) : (Coord C d → ℂ) →L[ℂ] (ι → ℂ) :=
  .pi fun i => ∑ j : Coord C d, B i j • ContinuousLinearMap.proj j

omit [Fintype ι] in
lemma pairMix_at (B : ι → C.label d) (p i) : pairMix (d := d) B p i = ∑ j : Coord C d, B i j * p j := by
  simp [pairMix]

omit [Fintype ι] in
lemma pairMix_agrees (B : ι → C.label d) (t : Test 2) (u : ℕ×ℕ) (x : C.label d) (i) :
    pairMix (d := d) B (observe (pairFamily C d t) d u x) i = scanPair C t d u x (B i) := by
  let L := secondScan (d := d) C t x u
  have he (j : Coord C d) : observe (pairFamily C d t) d u x j = L (Pi.single j 1) :=
    (pair_snap C t d u x (Pi.single j 1)).symm.trans (second_scan (d := d) t x _ u).symm
  rw [pairMix_at, ← second_scan (d := d)]
  change ∑ j : Coord C d, B i j • (observe (pairFamily C d t) d u x) j = L _
  simp_rw [he, ← L.map_smul, ← map_sum]
  congr 1
  simp_rw [← Pi.single_smul',smul_eq_mul,mul_one]
  exact Finset.univ_sum_single (B i)

variable {V Z : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z] [FiniteDimensional ℂ Z]

omit [FiniteDimensional ℂ V] in
lemma cost_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {T : ℕ×ℕ → V} (L : V →L[ℂ] E) (hT : cost f T) : cost f (fun u => L (T u)) := by
  obtain ⟨D,hD,hT⟩ := hT
  refine ⟨(‖L‖+1)*D,by positivity,?_⟩
  filter_upwards [hT] with u hu
  exact (L.le_opNorm _).trans (by gcongr; simp)

lemma cost_X (β : Module.Basis ι ℂ V) (T : ℕ×ℕ → ι → C.label d) (hT : cost f T) :
    cost f (fun u => LinearMap.toContinuousLinearMap (β.constr ℂ (T u))) := by
  let A : (ι → C.label d) →ₗ[ℂ] (V →L[ℂ] C.label d) := LinearMap.toContinuousLinearMap.toLinearMap.comp (β.constr ℂ).toLinearMap
  exact cost_clm (LinearMap.toContinuousLinearMap A) hT

lemma cost_B (T : ℕ×ℕ → ι → C.label d) (hT : cost f T) : cost f (fun u => pairMix (d := d) (T u)) := by
  let L : (ι → C.label d) →ₗ[ℂ] (Coord C d → ℂ) →L[ℂ] (ι → ℂ) :=
    { toFun := pairMix (d := d)
      map_add' := by intro v w; ext x j; simp [pairMix_at,add_mul,Finset.sum_add_distrib]
      map_smul' := by intro c w; ext x j; simp [pairMix_at,Finset.mul_sum,mul_assoc] }
  exact cost_clm (LinearMap.toContinuousLinearMap L) hT

lemma matrix_tends {α : Type*} {F : Filter α} (H : Module.Basis ι ℂ V)
    {L : α → V →L[ℂ] Z} {W : V →L[ℂ] Z} (h : ∀ i, Tendsto (fun x => L x (H i)) F (𝓝 (W (H i)))) : Tendsto L F (𝓝 W) := by
  refine fit_plane (fun x => (L x).toLinearMap) W.toLinearMap fun v => ?_
  have he (A : V →L[ℂ] Z) : A v = ∑ j, H.repr v j • A (H j) := by
    conv_lhs => arg 2; rw [← H.sum_repr v]
    rw [map_sum]; simp_rw [map_smul]
  change Tendsto (fun x => L x v) F (𝓝 (W v))
  simp_rw [he]
  exact tendsto_finsetSum _ fun i _ => tendsto_const_nhds.smul (h i)

open Classical in
/-- Freeze one test shape per k. The comparison here is entrywise on normalized
Wilson moments for pairs of calibrated basis coefficients, NOT evaluations of
vectors constrained to project onto a given moving subspace. Coefficient bound
is only at fixed k (no ∀k uniformity). Shot family uses fixed coordinate labels;
`ξ` can depend on both N and p, and is held fixed across the kernel positions. -/
theorem pairs_eventually (H : V →L[ℂ] (ι → ℂ)) (hi : Injective H)
    (β : Module.Basis ι ℂ V) (T : ℕ → Test 2) (ξ : ℕ → ℕ×ℕ → ι → C.label d)
    (hr : ∀ᶠ u in f.fuse, Module.finrank ℂ (LinearMap.range (b.step d u).toLinearMap) ≤ Module.finrank ℂ V)
    (hs : Silent b f d) (hp : cost f (b.step d)) (hd : ∀ᶠ k in atTop, cost f (ξ k))
    (he : ∀ i j, Tendsto (fun q : ℕ×(ℕ×ℕ) => scanPair C (T q.1) d q.2 (ξ q.1 q.2 i) (ξ q.1 q.2 j)) (deep f) (𝓝 (H (β i) j))) :
    ∀ᶠ k in atTop, ∃ c : ℝ, 0 < c ∧ ∀ᶠ u in f.fuse,
      ∀ v : C.label d, b.step d u v = v → c * ‖v‖ ≤ ∑ i ∈ Finset.univ.image (pairFamily C d (T k)), ‖snapshots i d u v‖ := by
  let X k u := LinearMap.toContinuousLinearMap (β.constr ℂ (ξ k u))
  apply eventual_bound H (fun k => pairFamily C d (T k)) (fun k u => pairMix (d := d) (ξ k u)) X hi hr hs hp
    (hd.mono fun k hk => cost_B (d := d) _ hk) (hd.mono fun k hk => cost_X (d := d) β _ hk)
  refine matrix_tends β fun i => tendsto_pi_nhds.mpr fun j => (he i j).congr' (Eventually.of_forall fun q => ?_)
  change _ = pairMix _ (observe (pairFamily C d (T q.1)) d q.2 (X q.1 q.2 (β i))) j
  rw [show (X q.1 q.2) (β i) = ξ q.1 q.2 i by simp [X], pairMix_agrees]
end YM.Push.FiniteDetection
