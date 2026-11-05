import YM.Bid.Angular

/-!
# A06: transport the finite collinear Ward test matrix

All statements conditional on their data. `test_aisle` is an exact
identity at each scale (pullback of the scenes); convergence of the
rows, on the other hand, will test at **fixed free coordinates** using
the prescribed jets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.A06
open Set Function Filter Org Climb Table Ward
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius NNReal InnerProductSpace

variable {G : Gauge} {L : Register G} {S : Table L} {n d : ℕ}

/-! ## Exact linearity of the rows. -/

private lemma diagram_smooth_at (H : S.Hierarchy) (s : Scene S d)
    (q : Climb.Matrix d (d+1) S) : ContDiffAt ℝ s.m (diagram s.v q) s.x := by
  unfold diagram
  exact ContDiffAt.sum fun i _ =>
    (cont_disc H _ s.strict).of_le (WithTop.coe_le_coe.mpr le_top)

-- Keep the `ContinuousSMul` inference abstract when making a row map.
private def asCLM {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [FiniteDimensional ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    (l : A →ₗ[ℝ] B) : A →L[ℝ] B := l.toContinuousLinearMap

/-- The Ward sum differentiated in the *position* variables is still
linear as a functional on the substitution matrices. Use smoothness on
Conf only; `observed` handles the possibly heterogeneous caps. -/
def lensL (H : S.Hierarchy) (s : Scene S d) : Climb.Vector d S →L[ℝ] ℂ := by
  let l : Climb.Vector d S →ₗ[ℝ] ℂ := {
    toFun := s.lens
    map_add' := fun p q => by
      have he : diagram s.v ((p+q) s.b) = diagram s.v (p s.b) + diagram s.v (q s.b) := by
        funext x
        simp only [Pi.add_apply, ← observation, map_add]
      change iteratedFDeriv ℝ s.m _ _ _ = _
      rw [he, iteratedFDeriv_add_apply (diagram_smooth_at H s _) (diagram_smooth_at H s _)]
      rfl
    map_smul' := fun c p => by
      have he : diagram s.v ((c • p : Climb.Vector d S) s.b) = c • diagram s.v (p s.b) := by
        funext x
        simp only [Pi.smul_apply, ← observation]
        exact ((observed s.v x (d+1)).restrictScalars ℝ).map_smul _ _
      change iteratedFDeriv ℝ s.m _ _ _ = _
      rw [he, iteratedFDeriv_const_smul_apply (diagram_smooth_at H s _)]
      rfl }
  exact asCLM (A:=Climb.Vector d S) (B:=ℂ) l

lemma lensL_apply (H : S.Hierarchy) (s : Scene S d) (p : Climb.Vector d S) : lensL H s p=s.lens p := rfl

private lemma smul_conf {r : ℝ} (hr : r≠0) {x : Points n} (hx : x ∈ conf n) : r • x ∈ conf n := by
  intro i j h
  apply (show Injective _ from hx)
  exact smul_right_injective _ hr (show r • x i = r • x j from h)

/-- Keep the directions the same here; `test_aisle` includes the
factor from scaling all `s.m` slots. -/
def scaledScene (X : Scaling S) (k : ℕ) (s : Scene (Bel L) d) : Scene S d where
  n := s.n
  v i := X.U k d (s.v i)
  a := s.a
  b := s.b
  offAxis := s.offAxis
  x := X.r k • s.x
  strict := smul_conf (X.positive k).ne' s.strict
  positions := fun i => by
    obtain ⟨t, ht⟩ := s.positions i
    refine ⟨X.r k * t,?_⟩
    change X.r k • s.x i = _
    rw [ht, smul_smul]
  m := s.m
  dirs := s.dirs

/-- Chain rule for the actual (nonzero) scale on Points. The linear
**equiv** version also works for functions only smooth on Conf. -/
lemma scaled_derivative (f : Points n → ℂ) (m : ℕ) {r : ℝ} (hr : r ≠ 0)
    (x : Points n) (dirs : Fin m → Points n) :
    iteratedFDeriv ℝ m (fun y => f (r • y)) x dirs = r ^ m • iteratedFDeriv ℝ m f (r • x) dirs := by
  let g : Points n ≃L[ℝ] Points n := ContinuousLinearEquiv.smulLeft (Units.mk0 r hr)
  have h := g.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (x := x) (mem_univ (g x)) m
  rw [preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  change iteratedFDeriv ℝ m (f ∘ g) x dirs = _
  rw [h]
  change iteratedFDeriv ℝ m f (r • x) (fun i => r • dirs i) = _
  simpa using (iteratedFDeriv ℝ m f (r • x)).map_smul_univ (fun _ => r) dirs

/-- Both target cap `d+1` and source cap `d` are transported. In
particular this does not independently calibrate any slot. -/
theorem test_aisle (X : Scaling S) (k : ℕ) (s : Scene (Bel L) d) (q : Climb.Vector d S) :
    X.test k s (X.aisle k d q) = X.r k ^ s.m • (scaledScene X k s).lens q := by
  have he (i : Fin s.n) :
      X.pins k ∘ update (column s.v) i (⟨d+1, X.aisle k d q s.b (s.v i)⟩ : (Bel L).Tag) =
      update (column (fun j : Fin s.n => X.U k d (s.v j))) i
        (⟨d+1, q s.b (X.U k d (s.v i))⟩ : S.Tag) := by
    funext j
    by_cases hij : j=i
    · subst j
      rw [comp_apply, update_self, update_self]
      change (⟨_, X.U k (d+1) (X.carry k (q s.b) (s.v i))⟩ : S.Tag)=_
      rw [Scaling.carries_f]
    · rw [comp_apply, update_of_ne hij, update_of_ne hij]
      rfl
  unfold Scaling.test
  simp_rw [he]
  exact scaled_derivative (diagram (scaledScene X k s).v (q s.b)) s.m (X.positive k).ne' s.x s.dirs

private lemma aisle_surj (X : Scaling S) (k d : ℕ) : Surjective (X.aisle k d) := by
  intro T
  let q : Climb.Vector d S := fun i => LinearMap.toContinuousLinearMap
    ((X.U k (d+1)).toLinearMap ∘ₗ ((T i).toLinearMap ∘ₗ (X.U k d).symm.toLinearMap))
  refine ⟨q,?_⟩
  ext1 i
  ext1 v
  apply (X.U k (d+1)).injective
  change X.U k _ (X.carry k (q i) v) = _
  rw [Scaling.carries_f]
  simp only [q]
  change X.U k _ (T i ((X.U k d).symm (X.U k d v))) = _
  rw [LinearEquiv.symm_apply_apply]

def testL (H : S.Hierarchy) (X : Scaling S) (k : ℕ) (s : Scene (Bel L) d) : V0 L d →L[ℝ] ℂ := by
  let l : V0 L d →ₗ[ℝ] ℂ := {
    toFun := X.test k s
    map_add' p q := by
      obtain ⟨p, rfl⟩ := aisle_surj X k d p
      obtain ⟨q, rfl⟩ := aisle_surj X k d q
      rw [← map_add, test_aisle, test_aisle, test_aisle]
      simp only [← lensL_apply H, map_add, smul_add]
    map_smul' c p := by
      obtain ⟨p, rfl⟩ := aisle_surj X k d p
      change _ = c • X.test k s _
      rw [← map_smul, test_aisle, test_aisle]
      simp only [← lensL_apply H, map_smul]
      exact smul_comm _ _ _ }
  exact asCLM (A:=V0 L d) (B:=ℂ) l

/-- Actual `Subs`, on all vectors (not just `Colors`). -/
def moved (H : S.Hierarchy) (X : Scaling S) (e : Select L d) : Subs e X where
  moves k := ContinuousLinearMap.pi fun i => testL H X k (e.rows i)
  values _ _ _ := rfl

lemma transverse_zero (X : Scaling S) (e : Select L d) (s : Subs e X)
    (p : Climb.Parts S) (hp : transverse p) (k : ℕ) : s.moves k (X.aisle k d (leaves p d)) = 0 := by
  funext i
  rw [s.values, test_aisle, hp]
  exact smul_zero ..

/-! ## Convergence of the rows. -/

/-- Evaluate on a *fixed* vector; only the given finite order on the
given window is used. -/
theorem test_limit (H : S.Hierarchy) (h : (Bel L).Hierarchy)
    (X : Scaling S) {N D m : ℕ} {R : ℝ} (hj : X.jets N D m R)
    (s : Scene (Bel L) d) (hN : s.n ≤ N) (hD : d+1 ≤ D) (hm : s.m ≤ m)
    (hR : s.x ∈ Scaling.window R s.n) (T : V0 L d) :
    Tendsto (fun k => X.test k s T) atTop (𝓝 (s.lens T)) := by
  let w (i : Fin s.n) := update (column s.v) i (⟨d+1, T s.b (s.v i)⟩ : (Bel L).Tag)
  let f (k : ℕ) (i : Fin s.n) (x : Points s.n) := disc (X.pins k ∘ w i) (X.r k • x)
  let F (i : Fin s.n) := disc (w i)
  have caps (i j : Fin s.n) : (w i j).1 ≤ D := by
    unfold w
    by_cases hh : j=i
    · subst j; rw [update_self]; exact hD
    rw [update_of_ne hh]
    exact (Nat.le_succ _).trans hD
  have hi (i : Fin s.n) : Tendsto (fun k => iteratedFDeriv ℝ s.m (f k i) s.x) atTop
      (𝓝 (iteratedFDeriv ℝ s.m (F i) s.x)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hj s.n hN s.m hm (w i) (caps i) (ε/2) (by positivity)] with k hk
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hk _ hR) (half_lt_self hε)
  have hf (k : ℕ) (i : Fin s.n) : ContDiffAt ℝ s.m (f k i) s.x :=
    ((cont_disc H _ (smul_conf (X.positive k).ne' s.strict)).of_le
      (WithTop.coe_le_coe.mpr le_top)).comp s.x (contDiffAt_id.const_smul (X.r k))
  have hF (i : Fin s.n) : ContDiffAt ℝ s.m (F i) s.x :=
    (cont_disc h _ s.strict).of_le (WithTop.coe_le_coe.mpr le_top)
  have he (k : ℕ) : iteratedFDeriv ℝ s.m (fun x => ∑ i, f k i x) s.x =
      ∑ i, iteratedFDeriv ℝ s.m (f k i) s.x :=
    iteratedFDeriv_fun_sum_apply (fun i _ => hf k i)
  have hlim : Tendsto (fun k => iteratedFDeriv ℝ s.m (fun x => ∑ i, f k i x) s.x) atTop
      (𝓝 (iteratedFDeriv ℝ s.m (fun x => ∑ i, F i x) s.x)) := by
    simp_rw [he]
    rw [iteratedFDeriv_fun_sum_apply (f:=F) (fun i _ => hF i)]
    exact tendsto_finsetSum _ (fun i _ => hi i)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ => Points s.n) ℂ s.dirs).continuous.continuousAt.tendsto.comp hlim

-- Real version of the finite-coordinate argument in Dash.fit_plane (on
-- continuous linear maps). Both spaces finite dimensional here.
private theorem clm_limit {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [FiniteDimensional ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    (f : ℕ → A →L[ℝ] B) (F : A →L[ℝ] B) (h : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (F x))) :
    Tendsto f atTop (𝓝 F) := by
  classical
  let b := Module.finBasis ℝ A
  let I := Fin (Module.finrank ℝ A)
  let L : (I → B) →ₗ[ℝ] A→L[ℝ] B := LinearMap.toContinuousLinearMap.toLinearMap.comp (b.constr ℝ).toLinearMap
  have he (g : A→L[ℝ] B) : L (fun i => g (b i)) = g := by
    apply ContinuousLinearMap.coe_injective
    exact b.ext fun i => b.constr_basis ..
  have hh := L.continuous_of_finiteDimensional.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr
    (show ∀ i,Tendsto (fun k => (fun j : I => f k (b j)) i) atTop (𝓝 ((fun j : I => F (b j)) i)) from fun i => h _))
  convert hh using 1
  · funext u
    exact (he (f u)).symm
  rw [he F]

lemma moves_limit (H : S.Hierarchy) (h : (Bel L).Hierarchy)
    (X : Scaling S) {N D m : ℕ} {R : ℝ} (hj : X.jets N D m R)
    (e : Select L d) (s : Subs e X) (hN : ∀ i,(e.rows i).n ≤ N) (hD : d+1 ≤ D) (hm : ∀ i,(e.rows i).m ≤ m)
    (hR : ∀ i,(e.rows i).x ∈ Scaling.window R (e.rows i).n) :
    Tendsto s.moves atTop (𝓝 e.reads) := by
  refine clm_limit (A:=V0 L d) (B:=Fin e.m → ℂ) s.moves e.reads fun x => ?_
  refine tendsto_pi_nhds.mpr fun i => ?_
  change Tendsto (fun k => s.moves k x i) atTop (𝓝 (e.reads x i))
  simp_rw [s.values, e.stimulated]
  exact test_limit H h X hj (e.rows i) (hN i) hD (hm i) (hR i) x

lemma eventually_window {x : Points n} (hx : x ∈ conf n) :
    ∀ᶠ R : ℝ in atTop, x ∈ Scaling.window R n := by
  have he (i j : Fin n) : ∀ᶠ R : ℝ in atTop, i≠j → R⁻¹ ≤ cubedist (x i) (x j) := by
    rcases eq_or_ne i j with h | h
    · exact Eventually.of_forall fun _ p => False.elim (p h)
    have hc : 0 < cubedist (x i) (x j) :=
      dist_pos.mpr fun w => h ((show Injective _ from hx) (WithLp.ofLp_injective _ w))
    filter_upwards [tendsto_inv_atTop_zero.eventually (gt_mem_nhds hc)] with R hR
    exact fun _ => le_of_lt hR
  exact (eventually_all.mpr (fun i => eventually_all.mpr (he i))).and (eventually_ge_atTop ‖x‖)

theorem answer : YM.Bid.A06 := by
  intro G C S H V _hin _hder R J d p hp hV _hc e _he
  -- Demand all target weights through d+1, only the maximum position
  -- arity and directional order of the rows, and one common window.
  let N := Finset.univ.sup fun i => (e.rows i).n
  let m := Finset.univ.sup fun i => (e.rows i).m
  have hw : ∀ᶠ B : ℝ in atTop, 1 ≤ B ∧ ∀ i, (e.rows i).x ∈ Scaling.window B (e.rows i).n :=
    (eventually_ge_atTop 1).and (eventually_all.mpr fun i => eventually_window (e.rows i).strict)
  obtain ⟨r,hr⟩ := eventually_atTop.mp hw
  refine ⟨d+1, N, m, r, (hr r le_rfl).1, ?_⟩
  intro X D n k B hD hN hm hB hX
  have hpath : d+1 ≤ max D 4 := hD.trans (le_max_left _ _)
  refine ⟨⟨fun i j h => hX.path.Hsym i j (h.trans hpath),
    fun i j h => hX.path.carries i j (h.trans hpath),
    fun i j l h hl v => hX.path.incl i j l h (hl.trans hpath) v⟩, moved H X e, ?_, ?_⟩
  · have hun (i) : (e.rows i).n ≤ N := Finset.le_sup (f:=fun i => (e.rows i).n) (Finset.mem_univ i)
    have hum (i) : (e.rows i).m ≤ m := Finset.le_sup (f:=fun i => (e.rows i).m) (Finset.mem_univ i)
    exact moves_limit H R.hT X hX.thick e (moved H X e) (fun i => (hun i).trans hN) hD
      (fun i => (hum i).trans hm) (hr B hB).2
  exact Eventually.of_forall fun i => ⟨transverse_zero X e (moved H X e) V.deriv hV i,
    transverse_zero X e (moved H X e) p hp i⟩

end YM.Work.A06
