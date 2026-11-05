import YM.Org.Input

/-!
Heterogeneous probes: choose enough of them *before* the Track request;
invert their readings even though the tests move with the weak system.
No unit or particular Maxwell label singled out here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.A05
open Set Function Filter Table Climb Ward
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

section FD
variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- Convenient CLM spelling of `Dash.fit_plane`. -/
lemma clm_convergence (A : ℕ → V →L[ℂ] F) (a : V →L[ℂ] F)
    (h : ∀ v, Tendsto (fun k => A k v) atTop (𝓝 (a v))) : Tendsto A atTop (𝓝 a) := by
  exact Dash.fit_plane (fun k => (A k).toLinearMap) a.toLinearMap h

lemma finite_separates {O : Type*} (t : O → V →ₗ[ℂ] ℂ)
    (ht : ∀ x y : V, (∀ o, t o x = t o y) → x = y) :
    ∃ s : Finset O, ∀ x y : V, (∀ o ∈ s, t o x = t o y) → x = y := by
  classical
  let K (s : Finset O) := ⨅ i : s, LinearMap.ker (t i)
  have hs (s : Finset O) (v : V) : v ∈ K s ↔ ∀ i ∈ s, t i v = 0 := by
    simp [K, Submodule.mem_iInf]
  let p : ℕ → Prop := fun n => ∃ s : Finset O, Module.finrank ℂ (K s) = n
  have H : ∃ n, p n := ⟨_, ∅, rfl⟩
  obtain ⟨s, hmin⟩ := (show p (Nat.find H) from Nat.find_spec H)
  have he (i : O) : K (insert i s) = K s := by
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · intro v hv
      exact (hs s v).2 fun j hj => (hs _ v).1 hv j (Finset.mem_insert_of_mem hj)
    · rw [hmin]; exact Nat.find_min' H (show p _ from ⟨insert i s, rfl⟩)
  refine ⟨s, fun x y h => ht x y fun i => ?_⟩
  have hx : x-y ∈ K s := (hs s _).2 (fun j hj => by rw [map_sub, h j hj, sub_self])
  have hy := (hs (insert i s) _).1 (show x-y ∈ K (insert i s) by rw [he]; exact hx)
  apply sub_eq_zero.mp
  rw [← map_sub]; exact hy i (Finset.mem_insert_self ..)

/-- Left inverse at the limit, then invert a near-identity square family. In
particular no bound on the sequence being tested has to be assumed. -/
lemma recover_clm (A : ℕ → V →L[ℂ] F) (a : V →L[ℂ] F) (ha : Injective a)
    (hA : Tendsto A atTop (𝓝 a)) (v : ℕ → V) (w : V)
    (hv : Tendsto (fun k => A k (v k)) atTop (𝓝 (a w))) : Tendsto v atTop (𝓝 w) := by
  let B := LinearMap.toContinuousLinearMap a.toLinearMap.leftInverse
  have hB (u : V) : B (a u) = u :=
    LinearMap.leftInverse_apply_of_inj ((LinearMap.ker_eq_bot (f := a.toLinearMap)).2 ha) u
  let D (k : ℕ) := B.comp (A k)
  have hD : Tendsto D atTop (𝓝 (1 : V →L[ℂ] V)) := by
    rw [← show B.comp a = 1 from ContinuousLinearMap.ext hB]
    exact (show Continuous (fun y : V →L[ℂ] F => B.comp y) from
      continuous_const.clm_comp continuous_id).continuousAt.tendsto.comp hA
  have he : Tendsto (fun k => D k (v k)) atTop (𝓝 w) := by
    have he : Tendsto (fun k => D k (v k)) atTop (𝓝 (B (a w))) :=
      B.continuous.continuousAt.tendsto.comp hv
    rwa [hB w] at he
  have hi : Tendsto (fun k => Ring.inverse (D k)) atTop (𝓝 (1 : V →L[ℂ] V)) := by
    have hh := NormedRing.inverse_continuousAt (1 : (V →L[ℂ] V)ˣ)
    change ContinuousAt Ring.inverse (1 : V →L[ℂ] V) at hh
    simpa only [Ring.inverse_one,Function.comp_def] using hh.tendsto.comp hD
  have hw : Tendsto (fun k => Ring.inverse (D k) (D k (v k))) atTop (𝓝 w) := Dash.arcing hi he
  apply hw.congr'
  filter_upwards [hD.eventually (Units.isOpen.mem_nhds isUnit_one)] with k hk
  exact congr_arg (fun g : V →L[ℂ] V => g (v k)) (Ring.inverse_mul_cancel _ hk)

lemma recover_on {O : Type*} (s : Finset O) (t : O → V →ₗ[ℂ] ℂ)
    (hs : ∀ x y : V, (∀ o ∈ s, t o x = t o y) → x = y) (u : O → ℕ → V →ₗ[ℂ] ℂ)
    (hu : ∀ o ∈ s, ∀ x, Tendsto (fun k => u o k x) atTop (𝓝 (t o x))) (v : ℕ → V) (w : V)
    (hv : ∀ o ∈ s, Tendsto (fun k => u o k (v k)) atTop (𝓝 (t o w))) : Tendsto v atTop (𝓝 w) := by
  classical
  let A (k : ℕ) := LinearMap.pi fun o : s => u o k
  let a := LinearMap.pi fun o : s => t o
  refine recover_clm (fun k => LinearMap.toContinuousLinearMap (A k))
    (LinearMap.toContinuousLinearMap a) ?_ (Dash.fit_plane A a ?_) v w ?_
  · exact fun x y h => hs x y fun o ho => congr_fun h (⟨o,ho⟩ : s)
  · exact fun x => tendsto_pi_nhds.mpr fun o : s => hu o o.property x
  · exact tendsto_pi_nhds.mpr fun o : s => hv o o.property
end FD

variable {G : Gauge} {L : Register G} {S : Table L} {n : ℕ}

def frontRead (x : Points (n+1)) (q : Fin n → S.Tag) (d : ℕ) : S.Field d →ₗ[ℂ] ℂ :=
  Ward.here (q := Fin.cons ⟨d,(0:S.Field d)⟩ q) x 0 d

lemma frontRead_at (x : Points (n+1)) (q : Fin n → S.Tag) (d : ℕ) (u : S.Field d) :
    frontRead x q d u = Ward.disc (Fin.cons ⟨d,u⟩ q) x := by
  unfold frontRead; rw [Ward.takes]; congr 1
  funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

lemma caps_cons_le {d D : ℕ} (B : S.Field d) (q : Fin n → S.Tag) (hd : d ≤ D)
    (hq : ∀ i, (q i).1 ≤ D) :
    ∀ i, ((Fin.cons (α := fun _ => S.Tag) ⟨d,B⟩ q) i).1 ≤ D := by
  intro i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [hd,hq]

lemma pins_cons (X : Climb.Scaling S) (k d : ℕ) (v : (Bel L).Field d) (q : Fin n → (Bel L).Tag) :
    X.pins k ∘ (Fin.cons ⟨d,v⟩ q) = (Fin.cons (α := fun _ => S.Tag) ⟨d,X.U k d v⟩ (X.pins k ∘ q)) := by
  funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp only [Function.comp_apply, Fin.cons_zero, Fin.cons_succ]
  rfl

/-- What order zero of `Scaling.jets` says on the same window. -/
lemma value_bound (X : Scaling S) {N D m : ℕ} {R : ℝ} (h : X.jets N D m R) (hn : n ≤ N)
    (v : Fin n → (Bel L).Tag) (hv : ∀ i, (v i).1 ≤ D) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ Scaling.window R n,
    ‖disc (X.pins k ∘ v) (X.r k • x) - disc v x‖ ≤ ε := by
  filter_upwards [h n hn 0 (Nat.zero_le _) v hv ε hε] with k hk
  intro x hx
  let F (z : Points n) := disc (X.pins k ∘ v) (X.r k • z)
  have he : iteratedFDeriv ℝ 0 F x - iteratedFDeriv ℝ 0 (disc v) x =
      iteratedFDeriv ℝ 0 (fun y => F y - disc v y) x := by
    ext1 y; simp
  have hh := hk x hx
  change ‖iteratedFDeriv ℝ 0 F x - iteratedFDeriv ℝ 0 (disc v) x‖ ≤ ε at hh
  rw [he,norm_iteratedFDeriv_zero] at hh; exact hh

/-- One heterogeneous exterior test. Includes the insertion point in `x` but
leaves its field slot open. -/
structure Observer (S : Table L) where
  n : ℕ
  x : Points (n+1)
  hx : x ∈ conf _
  q : Fin n → S.Tag

namespace Observer

def test (o : Observer S) (d : ℕ) := frontRead o.x o.q d

def moving (o : Observer (Bel L)) (X : Scaling S) (d k : ℕ) : (Bel L).Field d →ₗ[ℂ] ℂ :=
  (frontRead (X.r k • o.x) (X.pins k ∘ o.q) d).comp (X.U k d).toLinearMap

lemma exists_reads (H : S.Hierarchy) (d : ℕ) :
    ∃ s : Finset (Observer S), ∀ u v : S.Field d, (∀ o ∈ s, o.test d u = o.test d v) → u=v := by
  apply finite_separates
  intro u v h
  apply S.field_ext H.laws.toSymmetric
  intro n q x hx
  have ht := h ⟨n,x,hx,q⟩
  change frontRead x q d u = frontRead x q d v at ht
  rw [frontRead_at,frontRead_at] at ht
  exact ht

lemma reads_converge (o : Observer (Bel L)) (X : Scaling S) {N D m : ℕ} {R : ℝ}
    (h : X.jets N D m R) (hn : o.n+1 ≤ N) (hq : ∀ i, (o.q i).1 ≤ D) (hx : o.x ∈ Scaling.window R _)
    (d : ℕ) (hd : d ≤ D) (v : (Bel L).Field d) :
    Tendsto (fun k => o.moving X d k v) atTop (𝓝 (o.test d v)) := by
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  filter_upwards [value_bound X h hn (Fin.cons ⟨d,v⟩ o.q) (caps_cons_le v o.q hd hq) (half_pos hε)] with k hk
  rw [dist_eq_norm]; apply lt_of_le_of_lt _ (half_lt_self hε)
  change ‖frontRead _ _ _ (X.U k d v) - frontRead _ _ _ v‖ ≤ _
  rw [frontRead_at,frontRead_at,← pins_cons]; exact hk _ hx
end Observer
end YM.Work.A05
