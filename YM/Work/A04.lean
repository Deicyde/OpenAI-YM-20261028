import YM.Bid.Angular
set_option autoImplicit false
noncomputable section
namespace YM.Work.A04
open Set Function Filter Org Bid Extraction Climb Table Ward Spin
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius NNReal InnerProductSpace

section Linear
variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- A finite set of tests suffices at each finite cap. -/
theorem finite_faithful (f : ι → E →ₗ[ℂ] ℂ) (hf : Injective (LinearMap.pi f)) :
    ∃ s : Finset ι, Injective (LinearMap.pi (fun i : s => f i)) := by
  classical
  let K (s : Finset ι) := LinearMap.ker (LinearMap.pi (fun i : s => f i))
  obtain ⟨_, ⟨s, rfl⟩, h⟩ := wellFounded_lt.has_min
    (Set.range (fun s : Finset ι => Module.finrank ℂ (K s))) (Set.range_nonempty _)
  refine ⟨s, LinearMap.ker_eq_bot.mp ?_⟩
  refine bot_unique (fun v (hv : v ∈ K s) => ?_)
  rw [← LinearMap.ker_eq_bot.mpr hf]
  apply LinearMap.mem_ker.mpr
  funext i
  have he : K (insert i s) = K s := by
    refine Submodule.eq_of_le_of_finrank_le ?_ (not_lt.mp (h _ (Set.mem_range_self (insert i s))))
    intro x hx
    apply funext
    exact fun j => congr_fun (show (LinearMap.pi _) x = 0 from hx)
      ⟨j.val, Finset.mem_insert_of_mem j.property⟩
  rw [← he] at hv
  exact congr_fun (show (LinearMap.pi _) v = 0 from hv) ⟨i, Finset.mem_insert_self ..⟩

/-- Fit a signal through varying linear tests whose limit is injective. -/
theorem tendsto_of_fitted (f : ℕ → E →ₗ[ℂ] F) (g : E →ₗ[ℂ] F)
    {w : ℕ → E} {z : E} (hg : Injective g) (hf : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (g x)))
    (hw : Tendsto (fun k => f k (w k)) atTop (𝓝 (g z))) : Tendsto w atTop (𝓝 z) := by
  obtain ⟨h, hh⟩ := g.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hg)
  have he (x : E) : h (g x) = x := LinearMap.congr_fun hh x
  let A (k : ℕ) : E →L[ℂ] E := LinearMap.toContinuousLinearMap (h.comp (f k))
  have hh' := h.continuous_of_finiteDimensional
  have ha : Tendsto A atTop (𝓝 1) := by
    change Tendsto _ _ (𝓝 (LinearMap.toContinuousLinearMap (LinearMap.id : E →ₗ[ℂ] E)))
    refine Dash.fit_plane _ _ (fun x => ?_)
    change Tendsto _ _ (𝓝 x)
    nth_rw 2 [← he x]
    exact (hh'.tendsto (g x)).comp (hf x)
  have hva : Tendsto (fun k => A k (w k)) atTop (𝓝 z) := by
    rw [← he z]; exact (hh'.tendsto _).comp hw
  have hi : Tendsto (fun k => Ring.inverse (A k)) atTop (𝓝 (1 : E →L[ℂ] E)) := by
    rw [← Ring.inverse_one (E →L[ℂ] E)]
    exact (NormedRing.inverse_continuousAt (1 : (E →L[ℂ] E)ˣ)).tendsto.comp ha
  have hv := Dash.arcing hi hva
  rw [one_apply_eq_self] at hv
  apply hv.congr'
  filter_upwards [ha.eventually (Units.nhds (1 : (E →L[ℂ] E)ˣ))] with k hk
  change (Ring.inverse (A k) * A k) (w k) = _
  rw [Ring.inverse_mul_cancel _ hk]; rfl
end Linear

variable {G : Gauge} {L : Register G} {S : Table L} {d n : ℕ}

/-- Free row at a separated exterior tuple and its varying version. -/
def row (S : Table L) (d : ℕ) (e : Exterior L) : S.Field d →ₗ[ℂ] ℂ :=
  (LinearMap.proj e).comp (S.spectra d)

theorem row_faithful (S : Table L) (d : ℕ) : Injective (LinearMap.pi (row S d)) := S.faithfully d

def tags (S : Table L) (e : Exterior L) (v : S.Field d) : Fin (e.n+1) → S.Tag :=
  Fin.cons ⟨d,v⟩ (S.classTokens ∘ e.letter)

theorem row_eq (h : S.Symmetric) (e : Exterior L) (v : S.Field d) :
    row S d e v = disc (tags S e v) e.point := (S.through h v _ e.clear).symm

def approxRow (p : Scaling S) (d : ℕ) (e : Exterior (Maxwell.standard L.grid)) (k : ℕ) : (Bel L).Field d →ₗ[ℂ] ℂ :=
  (here (p.pins k ∘ tags (Bel L) e (0 : (Bel L).Field d)) (p.r k • e.point) 0 d).comp (p.U k d).toLinearMap

theorem approxRow_eq (p : Scaling S) (e : Exterior (Maxwell.standard L.grid)) (k : ℕ) (v : (Bel L).Field d) :
    approxRow p d e k v = disc (p.pins k ∘ tags (Bel L) e v) (p.r k • e.point) := by
  rw [approxRow, LinearMap.comp_apply, takes]
  simp only [tags, Fin.comp_cons, Fin.update_cons_zero, Scaling.pins]
  rfl

theorem jetsAt (p : Scaling S) {N D m j : ℕ} {B : ℝ} (h : p.jets N D m B)
    (hn : n ≤ N) (hj : j ≤ m) {v : Fin n → (Bel L).Tag}
    (hv : ∀ i, (v i).1 ≤ D) {x : Points n} (hx : x ∈ Scaling.window B n) (u : Fin j → Points n) :
    Tendsto (fun k => iteratedFDeriv ℝ j (fun y => disc (p.pins k ∘ v) (p.r k • y)) x u)
      atTop (𝓝 (iteratedFDeriv ℝ j (disc v) x u)) := by
  have he : Tendsto (fun k => iteratedFDeriv ℝ j (fun y => disc (p.pins k ∘ v) (p.r k • y)) x)
      atTop (𝓝 (iteratedFDeriv ℝ j (disc v) x)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [h _ hn _ hj v hv _ (half_pos hε)] with k hk
    rw [dist_eq_norm]; exact (hk _ hx).trans_lt (half_lt_self hε)
  exact (ContinuousMultilinearMap.apply ℝ _ _ u).continuous.continuousAt.tendsto.comp he

theorem tags_cap {e : Exterior L} {D : ℕ} (hd : d ≤ D) (h : ∀ i, (e.letter i).1 ≤ D) (v : S.Field d) :
    ∀ i, ((tags S e v) i).1 ≤ D := Fin.cases hd h

theorem tendsto_row (p : Scaling S) (hB : (Bel L).Symmetric) {e : Exterior (Maxwell.standard L.grid)}
    {D N m : ℕ} {B : ℝ} (h : p.jets N D m B)
    (hn : e.n+1 ≤ N) (hd : d ≤ D) (hD : ∀ i, (e.letter i).1 ≤ D) (hx : e.point ∈ Scaling.window B (e.n+1)) :
    ∀ v, Tendsto (fun k => approxRow p d e k v) atTop (𝓝 (row (Bel L) d e v)) := by
  intro v
  simp only [approxRow_eq, row_eq hB]
  simpa only [iteratedFDeriv_zero_apply] using!
    jetsAt p h hn (Nat.zero_le m) (tags_cap hd hD v) hx (fun _ => 0)

theorem scale_conf (r : ℝ) (hr : 0 < r) {x : Points n} (hx : x ∈ conf n) : r • x ∈ conf n := by
  intro i j hij
  exact hx (smul_right_injective E4 hr.ne' (show r • x i = r • x j from hij))

theorem gradient_scaled (r : ℝ) (f : Points n → ℂ) (x : Points n) (hf : DifferentiableAt ℝ f (r • x))
    (i : Fin n) (a : Axis) : Points.gradient i a (fun y => f (r • y)) x = r • Points.gradient i a f (r • x) := by
  let R := r • ContinuousLinearMap.id ℝ (Points n)
  change fderiv ℝ (f ∘ R) x _ = _
  rw [fderiv_comp x (show DifferentiableAt ℝ f (R x) from hf) R.differentiableAt, R.fderiv,
    ContinuousLinearMap.comp_apply]
  exact (fderiv ℝ f (r • x)).map_smul r _

/-- Evaluation after carrying and scaling the derivative is exactly a derivative in the rescaled positions. -/
theorem approxDeriv (H : S.Hierarchy) (V : DiffPlan S) (hV : V.Derivatives S)
    (p : Scaling S) (e : Exterior (Maxwell.standard L.grid)) (a : Axis) (v : (Bel L).Field d) (k : ℕ) :
    approxRow p (d+1) e k ((p.r k • p.aisle k d (leaves V.deriv d)) a v) =
      Points.gradient 0 a (fun y => disc (p.pins k ∘ tags (Bel L) e v) (p.r k • y)) e.point := by
  rw [approxRow_eq]
  let y := p.r k • e.point
  let w := (p.pins k ∘ tags (Bel L) e v)
  have hy : y ∈ conf _ := scale_conf _ (p.positive k) e.clear
  rw [gradient_scaled (p.r k) (disc w) _ ((cont_disc H _ hy).differentiableAt (by simp))]
  simp only [w, tags, Fin.comp_cons]
  have he (z : (Bel L).Field (d+1)) : p.U k (d+1) (p.r k • z) = p.r k • p.U k (d+1) z :=
    ((p.U k (d+1)).toLinearMap.restrictScalars ℝ).map_smul _ _
  let l := (p.pins k ∘ ((Bel L).classTokens ∘ e.letter))
  change disc (Fin.cons ⟨_,p.U k (d+1) (p.r k • p.carry k (leaves V.deriv d a) v)⟩ l) y =
    p.r k • Points.gradient 0 a (disc (Fin.cons ⟨d,p.U k d v⟩ l)) y
  rw [he,p.carries_f]; unfold disc; rw [← hV.kernels d a (p.U k d v) hy l]
  let z := V.deriv d a (p.U k d v)
  have H (v : S.Field (d+1)) : disc (Fin.cons ⟨d+1,v⟩ l) y = here (Fin.cons ⟨d+1,z⟩ l) y 0 (d+1) v := by
    rw [takes, Fin.update_cons_zero]
  exact (H _).trans ((((here _ _ _ _).restrictScalars ℝ).map_smul _ z).trans (congr_arg _ (H z).symm))

theorem tendsto_deriv_row (H : S.Hierarchy) (V : DiffPlan S) (hV : V.Derivatives S)
    (hB : (Bel L).Symmetric) (W : DiffPlan (Bel L)) (hW : W.Derivatives (Bel L))
    (p : Scaling S) {e : Exterior (Maxwell.standard L.grid)}
    {D N m : ℕ} {B : ℝ} (h : p.jets N D m B)
    (hn : e.n+1 ≤ N) (hd : d ≤ D) (hD : ∀ i, (e.letter i).1 ≤ D) (hm : 1 ≤ m)
    (hx : e.point ∈ Scaling.window B (e.n+1)) (a : Axis) (v : (Bel L).Field d) :
    Tendsto (fun k => approxRow p (d+1) e k ((p.r k • p.aisle k d (leaves V.deriv d)) a v))
      atTop (𝓝 (row (Bel L) (d+1) e ((leaves W.deriv d) a v))) := by
  simp only [approxDeriv H V hV, row_eq hB]
  change Tendsto _ _ (𝓝 ((Bel L).useAt (Bel L) e.point (Fin.cons ⟨d+1,W.deriv d a v⟩ _)))
  rw [hW.kernels _ _ _ e.clear]
  simpa only [iteratedFDeriv_one_apply] using! jetsAt p h hn hm (tags_cap hd hD v) hx (fun _ => Points.direction 0 a)

theorem eventually_window {x : Points n} (hx : x ∈ conf n) :
    ∀ᶠ B in (atTop : Filter ℝ), x ∈ Scaling.window B n := by
  have he : ∀ᶠ B in (atTop : Filter ℝ), ∀ i j : Fin n, (cubedist (x i) (x j))⁻¹ ≤ B :=
    eventually_all.mpr fun _ => eventually_all.mpr fun _ => eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop (1 : ℝ), he, eventually_ge_atTop ‖x‖] with B hB he h
  refine ⟨fun i j hij => (inv_le_comm₀ (zero_lt_one.trans_le hB) ?_).mpr (he i j),h⟩
  exact dist_pos.mpr (fun he => hij (hx (congr_arg (WithLp.toLp 2) he)))

theorem answer : YM.Bid.A04 := by
  intro G C S H V _ hV R J d
  obtain ⟨s, hs⟩ := finite_faithful _ (row_faithful (Bel C.book) (d+1))
  obtain ⟨N, hN⟩ := (eventually_all.mpr fun i : s => eventually_ge_atTop (i.val.n+1)).exists
  have hD : ∀ᶠ D in (atTop : Filter ℕ), ∀ i : s, ∀ j, (i.val.letter j).1 ≤ D :=
    eventually_all.mpr fun _ => eventually_all.mpr fun _ => eventually_ge_atTop _
  obtain ⟨D, hd, hD⟩ := ((eventually_ge_atTop (d+1)).and hD).exists
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (1 : ℝ)).and (eventually_all.mpr fun i : s => eventually_window i.val.clear))
  refine ⟨D,N,1,B,(hB B le_rfl).1,fun p D' N' m B' hD' hN' hm hB' h => ?_⟩
  unfold ConLap
  apply tendsto_pi_nhds.mpr; intro a
  apply Dash.fit_plane (fun k => ((p.r k • p.aisle k d (leaves V.deriv d)) a).toLinearMap) (R.T.W.deriv d a)
  intro v
  apply tendsto_of_fitted (fun k => LinearMap.pi fun i : s => approxRow p (d+1) i.val k) _ hs
  · intro x; refine tendsto_pi_nhds.mpr fun i => ?_
    exact tendsto_row p R.hT.laws.toSymmetric h.thick ((hN i).trans hN') (hd.trans hD')
      (fun j => (hD i j).trans hD') ((hB B' hB').2 i) x
  refine tendsto_pi_nhds.mpr fun i => ?_
  exact tendsto_deriv_row H V hV R.hT.laws.toSymmetric R.T.W R.lit.pales p h.thick
    ((hN i).trans hN') (by omega) (fun j => (hD i j).trans hD') hm ((hB B' hB').2 i) a v
end YM.Work.A04
