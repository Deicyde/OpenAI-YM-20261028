import YM.Push.STRESS_FLUX.Conserved
import YM.Work.A04

/-!
# Normalization on weak schemes (conditional on the NONstress weak comparison)

E Cor.

No lower bound on xi.

Preserve r, all the maps on the same subsequence.

The argument can keep one choice of sign across finite demands.

No free derivative readout
assumption used.

No line-Ward or continuous rotation identity on S used.

This is a comparison
on the limiting Table; obtaining aligned weak schemes without stress from the finite lattice is
a separate and *not* established requirement.
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux
open Function Set Filter Gauge Table Climb Analysis
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace ContDiff
variable {G : Gauge} {L : Register G} {S : Table L} {T : DiffPlan (Bel L)} {V : DiffPlan S}
variable {A : S.RealSpin} {H : (Bel L).RealSpin}
variable {n N d m : ℕ} {R : ℝ}

/-- All maps below given **before** knowing any flux law or the rotation generators in S. -/
structure Scheme (X : Scaling S) (P : DiffPlan S) (T : DiffPlan (Bel L)) (A : S.RealSpin) (H : (Bel L).RealSpin) (N d m : ℕ) (R : ℝ) : Prop where
  path : X.Align P T A H (max d 4)
  thick : X.jets N d m R

lemma window_mono {B r : ℝ} (hr : 1 ≤ r) (hB : r ≤ B) : Scaling.window r n ⊆ Scaling.window B n :=
  fun _ hx => ⟨fun i j h => (inv_anti₀ (zero_lt_one.trans_le hr) hB).trans (hx.1 i j h),hx.2.trans hB⟩
lemma Scheme.mono {X : Scaling S} (h : Scheme X V T A H N d m R) {l d' m' : ℕ} {B : ℝ}
    (hn : l≤N) (hd : d'≤d) (hm : m'≤m) (hB : 1 ≤ B) (ht : B ≤ R) : Scheme X V T A H l d' m' B := by
  have hw : max d' 4 ≤ max d 4 := by omega
  exact ⟨⟨fun k d h1 => h.path.Hsym k d (h1.trans hw),fun k d h1 => h.path.carries k d (h1.trans hw),fun _ _ _ _ h1 => h.path.incl _ _ _ _ (h1.trans hw)⟩,
    fun n hl j he v hv ε hε => (h.thick n (hl.trans hn) j (he.trans hm) v (fun i => (hv i).trans hd) ε hε).mono fun _ hk x hx => hk x (window_mono hB ht hx)⟩

def updateScale (X : Scaling S) (φ : ℕ → ℕ) (hφ : StrictMono φ) (xi : ℕ → ℝ) (hx : ∀ k, 0 < xi k) : Scaling S where
  U k := X.U (φ k)
  r := X.r ∘ φ
  xi k := xi (φ k)
  later := X.later.comp_strictMono hφ
  positive k := X.positive (φ k)
  sign k := hx (φ k)
  drips := X.drips.comp hφ.tendsto_atTop

lemma Scheme.update {X : Scaling S} (h : Scheme X V T A H N d m R) (φ) (hφ : StrictMono φ) (xi hx) :
    Scheme (updateScale X φ hφ xi hx) V T A H N d m R :=
  ⟨⟨fun k => h.path.Hsym (φ k), fun k => h.path.carries (φ k), fun k => h.path.incl (φ k)⟩, fun n hn j hj v hv ε hε =>
    hφ.tendsto_atTop.eventually (h.thick n hn j hj v hv ε hε)⟩

private lemma varying {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (P : ℕ → E →ₗ[ℂ] ℂ) (g : E → ℂ) (H : ∀ x, Tendsto (fun k => P k x) atTop (𝓝 (g x))) {v w}
    (h : Tendsto v atTop (𝓝 w)) : Tendsto (fun k => P k (v k)) atTop (𝓝 (g w)) := by
  let L : E →ₗ[ℂ] ℂ := {
    toFun := g
    map_add' x y := tendsto_nhds_unique ((H (x+y)).congr fun _ => map_add _ x y) ((H x).add (H y))
    map_smul' c x := tendsto_nhds_unique ((H (c • x)).congr fun _ => map_smul _ c x) (tendsto_const_nhds.smul (H x)) }
  exact Dash.arcing (Dash.fit_plane P L H) h

private lemma coord_cont (w : ℕ → Coeff) {v} (h : Tendsto w atTop (𝓝 v)) (a b : Axis) :
    Tendsto (fun k => material S (w k) a b) atTop (𝓝 (material S v a b)) := by
  let L := fromPol S (d:=4) ∘ₗ (LinearMap.proj b) ∘ₗ (LinearMap.proj a) ∘ₗ stress G
  exact L.continuous_of_finiteDimensional.continuousAt.tendsto.comp h

private abbrev base := basis (0:Axis)
private lemma test_fits : ∀ᶠ R : ℝ in atTop, (0:Points 1) ∈ Scaling.window R 1 ∧ axisLine base ∈ Scaling.window R 2 :=
  (Work.A04.eventually_window (x:=(0:Points 1)) (fun _ _ _ => Subsingleton.elim ..)).and
    (Work.A04.eventually_window (axisLine_in base_ne))

lemma varied_vacuum {X : Scaling S} (hX : X.jets N d m R) (hN : 1 ≤ N) (hD : 4 ≤ d) (hR : (0:Points 1) ∈ Scaling.window R 1)
    (v : ℕ → (Bel L).Field 4) (w : (Bel L).Field 4) (h : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun k => average S (d:=4) 0 (X.U k 4 (v k))) atTop (𝓝 (average (Bel L) 0 w)) := by
  apply varying (fun k => (average S 0).comp (X.U k 4).toLinearMap) _ _ h
  intro p
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,← show ∀ (x : S.Field 4), oneStress S (fun _ _ => x) 0 0 0 = average S 0 x from fun _ => average_at ..,
    ← average_at (fun _ _ => p) 0 0 0]
  convert Work.A04.jetsAt X hX hN (Nat.zero_le m) (v:=fun _ => (⟨4,p⟩ : (Bel L).Tag)) (fun _ => hD) hR (fun _ => 0) using 1
  all_goals simp; rfl

def sped (V : DiffPlan S) (x : Points 2) (q : S.Tag) (a : Axis) : S.Field 4 →ₗ[ℂ] ℂ := (Work.A01.frontRead ![q] x (4+1)).comp (V.deriv 4 a)

private lemma sped_scale (V : DiffPlan S) (H : S.Hierarchy) (hV : V.Derivatives S) (x : Points 2) (hx : x∈conf _) (r : ℝ) (hr : 0 < r)
    (a : Axis) (v q : S.Field 4) : r • sped V (r • x) ⟨4,q⟩ a v = Points.gradient 0 a (fun y => quad S (r • y) ![v,q]) x := by
  let w := Fin.cons (α:=fun _ : Fin 2 => S.Tag) ⟨4,v⟩ ![⟨4,q⟩]
  have he : (fun i => (⟨4,(![v,q] : Fin 2 → S.Field 4) i⟩ : S.Tag)) = w := funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩)
  have hy := Work.A04.scale_conf r hr hx
  rw [sped,LinearMap.comp_apply, Work.A01.front_eval, hV.kernels 4 a v hy ![⟨4,q⟩]]; change r • Points.gradient 0 a (Ward.disc w) (r • x) = _
  rw [← Work.A04.gradient_scaled r (Ward.disc w) x ((Ward.cont_disc H w hy).differentiableAt (by simp))]
  unfold quad; rw [he]; rfl

def lineCLM : E4 →L[ℝ] Points 2 := LinearMap.toContinuousLinearMap {
  toFun := axisLine
  map_add' := fun _ _ => PiLp.ext
    (Fin.forall_fin_two.mpr ⟨rfl,show 0=(0:E4)+0 from (zero_add _).symm⟩)
  map_smul' r _ := PiLp.ext (Fin.forall_fin_two.mpr ⟨rfl, (smul_zero r).symm⟩) }

lemma gradient_base (h : S.Smooth) (a : Axis) (v q : S.Field 4) :
    Points.gradient 0 a (fun y => quad S y ![v,q]) (axisLine base) = Maxwell.grad a (fun z => quad S (axisLine z) ![v,q]) base := by
  let f := fun y => quad S y ![v,q]
  have hx : lineCLM base ∈ conf _ := axisLine_in base_ne
  have hf : DifferentiableAt ℝ f (lineCLM base) := ((S.class_smooth S h _).contDiffAt ((conf_open _).mem_nhds hx)).differentiableAt (by simp)
  symm; change fderiv ℝ (f ∘ lineCLM) base (basis a) = _
  rw [fderiv_comp _ hf lineCLM.differentiableAt,lineCLM.fderiv, ContinuousLinearMap.comp_apply,
      show lineCLM (basis a) = Points.direction (0:Fin 2) a from PiLp.ext (by intro i; fin_cases i <;> simp [lineCLM,axisLine, Points.direction])]; rfl

theorem varied_sped {X : Scaling S} (hX : X.jets N d m R) (hN : 2 ≤ N) (hD : 4 ≤ d) (hm : 1 ≤ m) (hR : axisLine base ∈ Scaling.window R 2)
    (H : S.Hierarchy) (V : DiffPlan S) (hV : V.Derivatives S)
    (a : Axis) (q : (Bel L).Field 4) (v : ℕ → (Bel L).Field 4) (w : (Bel L).Field 4) (h : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun k => X.r k • sped V (X.r k • axisLine base) ⟨4,X.U k 4 q⟩ a (X.U k 4 (v k))) atTop
      (𝓝 (Maxwell.grad a (fun z => quad (Bel L) (axisLine z) ![w,q]) base)) := by
  apply varying (fun k => X.r k • ((sped V (X.r k • axisLine base) ⟨4,X.U k 4 q⟩ a).comp (X.U k 4).toLinearMap))
    (fun w => Maxwell.grad a (fun z => quad (Bel L) (axisLine z) ![w,q]) base) _ h
  intro p
  let f : Fin 2 → (Bel L).Tag := fun i => ⟨4, (![p,q] : Fin 2 → (Bel L).Field 4) i⟩
  have he := Work.A04.jetsAt X hX hN hm (v:=f) (fun _ => hD) hR (fun _ => Points.direction 0 a)
  simp only [iteratedFDeriv_one_apply] at he
  have hq k y : Ward.disc (X.pins k ∘ f) y = quad S y ![X.U k 4 p, X.U k 4 q] := congr_arg (S.useAt S y) (funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩))
  simp_rw [hq] at he
  rw [← gradient_base (Maxwell.table_smooth L.grid)]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply,LinearEquiv.coe_coe,sped_scale V H hV (axisLine base) (axisLine_in base_ne) _ (X.positive _)]
  exact he

lemma tensor_pull {X : Scaling S} (h : ∀ k, Spin.realH A H (X.U k 4)) {J : S.Stress} (he : J∈TableTwo A) (k : ℕ) :
    (fun a b => (X.U k 4).symm (J a b)) ∈ TableTwo H := by
  let U := X.U k 4
  let L := U.symm.toLinearMap.restrictScalars ℝ
  have hu a b : U ((X.U k 4).symm (J a b)) = J a b := U.apply_symm_apply _
  refine ⟨fun a b => congr_arg U.symm (he.1 a b),fun a b => U.injective ?_,fun s a b => U.injective ?_⟩
  · rw [show ∀ v, U (conjQ H v) = conjQ A (U v) from (h k).2,hu, he.2.1]
  rw [show ∀ v, U (spinQ H s v) = spinQ A s (U v) from (h k).1 s,
    show U ((_ : ℝ) • (X.U k 4).symm (J (s.perm a) (s.perm b))) = (sign s a* sign s b) • U (U.symm _) from (U.toLinearMap.restrictScalars ℝ).map_smul _ _, hu,hu,he.2.2]

lemma weyl_nonzero : weyl ≠ 0 := by intro e; simpa [weyl] using congr_fun e 3

/-- Extraction of normalized coordinates of J itself. Normalization
factor not divided into any uncontrolled limit estimate. -/
theorem along {X : Scaling S} (h : G.Simple) (H' : S.Hierarchy) (hV : V.Derivatives S) (hX : Scheme X V T H'.spin H N d m R)
    (hn : 2≤N) (hd : 4≤d) (hm : 1≤m) (hR : (0:Points 1)∈Scaling.window R 1 ∧ axisLine base ∈ Scaling.window R 2)
    (J : S.Stress) (hp : J ∈ TableTwo H'.spin) (hc : Centers J) (he : nabla V J = 0) :
    ∃ φ hφ xi hx, let Y := updateScale X φ hφ xi hx
                  Y.meter J (material (Bel L) weyl) ∨ Y.meter J (material (Bel L) (-weyl)) := by
  have hU := tensor_pull (X:=X) (fun k => hX.path.Hsym k 4 (le_max_right ..)) hp
  choose c hq using fun k => (free_stress_bij h H).2 ⟨_,hU k⟩
  have hp k a b : X.U k 4 (material (Bel L) (c k) a b) = J a b := by
    rw [show material (Bel L) (c k) a b = (X.U k 4).symm (J a b) from congr_fun (congr_fun (congr_arg Subtype.val (hq k)) a) b,
      LinearEquiv.apply_symm_apply]
  have hn' k : 0 < ‖c k‖ := norm_pos_iff.mpr fun e => hc.alive <| funext fun a => funext fun b => by simpa [material,e] using (hp k a b).symm
  let fac (k : ℕ) := ‖weyl‖ * ‖c k‖⁻¹
  let u (k : ℕ) := fac k • c k
  have ht k : 0< fac k := mul_pos (norm_pos_iff.mpr weyl_nonzero) (inv_pos.mpr (hn' k))
  have htu k : u k ∈ Metric.sphere (0:Coeff) ‖weyl‖ := by
    simp [u,norm_smul,Real.norm_of_nonneg (ht k).le,fac,(hn' k).ne']
  obtain ⟨v,hv,φ,hφ,hz⟩ := (isCompact_sphere (0:Coeff) ‖weyl‖).isSeqCompact htu
  rw [Metric.mem_sphere,dist_zero_right] at hv
  let xi k := X.r k^4 / fac k
  have hx k : 0 < xi k := div_pos (pow_pos (X.positive k) _) (ht k)
  let Y := updateScale X φ hφ xi hx
  have hY : Scheme Y V T H'.spin H N d m R := hX.update ..
  let b (k : ℕ) := material (Bel L) (u (φ k))
  have hmtr k a i : Y.U k 4 (b k a i) = fac (φ k) • J a i := by
    unfold b u material
    simp only [map_smul,Pi.smul_apply]
    rw [show ∀ v, Y.U k 4 (fac (φ k) • v) = fac (φ k) • (Y.U k 4 v) from fun v => ((Y.U k 4).toLinearMap.restrictScalars ℝ).map_smul _ v]
    exact congr_arg _ (hp (φ k) a i)
  have hr a i : Tendsto (fun k => b k a i) atTop (𝓝 (material (Bel L) v a i)) := coord_cont _ hz a i
  have hm0 : Y.meter J (material (Bel L) v) := fun a i => by
    refine (hr a i).congr fun k => (Y.U k 4).injective ?_
    rw [hmtr, LinearEquiv.apply_symm_apply, show (↑((Y.xi k)⁻¹ * Y.r k ^ 4) : ℂ) = fac (φ k) by
      change (↑((X.r (φ k)^4 / fac (φ k))⁻¹ * X.r (φ k)^4):ℂ) = _; congr 1; field_simp [(X.positive _).ne', (ht _).ne']]
    exact (IsScalarTower.algebraMap_smul ℂ ..).symm
  have hzero : v 0=0 := by
    have hl := varied_vacuum hY.thick (by omega : 1 ≤ N) hd hR.1 _ _ (hr 0 0)
    simp only [hmtr,← average_at, oneStress_formula] at hl
    have hp k : average S (d:=4) 0 (fac (φ k) • J 0 0) = 0 := by
      rw [← IsScalarTower.algebraMap_smul ℂ (fac _) (J 0 0),map_smul, ← average_at, hc.center,smul_zero]
    exact Complex.ofReal_eq_zero.mp (tendsto_nhds_unique_of_eventuallyEq hl tendsto_const_nhds (Eventually.of_forall hp))
  have hd0 (i j : Axis) : (∑ a, Maxwell.grad a (signal L v i j i j a 0) base) = 0 := by
    let p := fromPol (Bel L) (pair G i j i j)
    have hl := tendsto_finsetSum Finset.univ (fun a _ => varied_sped hY.thick hn hd hm hR.2 H' V hV a p _ _ (hr a 0))
    simp_rw [hmtr, sped, LinearMap.comp_apply, ← IsScalarTower.algebraMap_smul ℂ (fac _) (J _ _), map_smul,
      ← Finset.smul_sum, ← map_sum,show ∑ a, V.deriv 4 a (J a 0) = 0 from congr_fun he 0, map_zero,smul_zero] at hl
    exact tendsto_nhds_unique hl tendsto_const_nhds
  have heq := div_kernel h v hzero hd0
  rw [heq,norm_smul] at hv
  have hs : ‖v 3‖ = (1:ℝ) := mul_right_cancel₀ (norm_ne_zero_iff.mpr weyl_nonzero) (hv.trans (one_mul _).symm)
  rcases eq_or_ne (v 3) 1 with hs'|hs'
  · rw [hs', one_smul] at heq; rw [heq] at hm0; exact ⟨φ,hφ,xi,hx,.inl hm0⟩
  have hl : v 3 = -1 := (abs_eq_abs.mp (show |v 3|=|(1:ℝ)| by simpa using hs)).resolve_left hs'
  rw [hl,neg_one_smul] at heq; rw [heq] at hm0; exact ⟨φ,hφ,xi,hx,.inr hm0⟩

lemma meter_neg {X : Scaling S} {J : S.Stress} {Q : (Bel L).Stress} (h : X.meter J Q) : X.meter (-J) (-Q) := fun a b => by
  simpa [Pi.neg_apply] using (h a b).neg
lemma meter_factor {X : Scaling S} {J : S.Stress} {Q : (Bel L).Stress} (h : X.meter J Q) {p : ℝ} (hp : 0 < p) :
    (updateScale X id strictMono_id (fun k => X.xi k / p) (fun k => div_pos (X.sign k) hp)).meter J (p • Q) := by
  intro a b; change Tendsto _ _ (𝓝 (p • Q a b))
  refine ((h a b).const_smul p).congr fun k => ?_
  change p • (X.U k 4).symm _ = (X.U k 4).symm (↑((X.xi k / p)⁻¹ * X.r k ^ 4) • J a b)
  rw [← show ∀ y, (X.U k 4).symm (p • y) = p • (X.U k 4).symm y from fun y => ((X.U k 4).symm.toLinearMap.restrictScalars ℝ).map_smul p y]
  congr 1
  rw [show ∀ t : ℝ, (t:ℂ) • J a b=t • J a b from (IsScalarTower.algebraMap_smul ℂ · _),
      smul_smul,inv_div]; congr 1; ring

def Nonstress (A : S.RealSpin) (V : DiffPlan S) (H : (Bel L).RealSpin) (T : DiffPlan (Bel L)) :=
    ∀ N d m : ℕ, ∀ R : ℝ, 1 ≤ R → ∃ X, Scheme X V T A H N d m R

private lemma cofinal_normalization (h : G.Simple) (A : S.Hierarchy) (hV : V.Derivatives S) (hs : Nonstress A.spin V H T)
    {J : S.Stress} (hp : J ∈ TableTwo A.spin) (hc : Centers J) (he : nabla V J = 0) :
    let L0 := material (Bel L) weyl
    ∃ Q : (Bel L).Stress, (Q=L0 ∨ Q=-L0) ∧ ∀ N d m R, 1 ≤ R → ∃ X, Scheme X V T A.spin H N d m R ∧ X.meter J Q := by
  intro L0
  let P (Q) (n : ℕ) := ∃ X, Scheme X V T A.spin H n n n n ∧ X.meter J Q
  have hv : ∀ᶠ n : ℕ in atTop, P L0 n ∨ P (-L0) n := by
    filter_upwards [eventually_ge_atTop 5,tendsto_natCast_atTop_atTop.eventually test_fits] with n hn ht
    obtain ⟨X,hX⟩ := hs n n n n (by exact_mod_cast (by omega : 1≤n))
    obtain ⟨φ,hφ,xi,hx,H1|H2⟩ := along h A hV hX (by omega) (by omega) (by omega) ht J hp hc he <;> unfold P
    · exact Or.inl ⟨_, hX.update .., H1⟩
    exact Or.inr ⟨_,hX.update .., (material_neg ..) ▸ H2⟩
  have hh (Q : (Bel L).Stress) (hq : ∃ᶠ n in atTop, P Q n) (N d m : ℕ) (R : ℝ) (hr : 1 ≤ R) : ∃ X, Scheme X V T A.spin H N d m R ∧ X.meter J Q := by
    obtain ⟨n,⟨X,hX,h⟩,hn,hd,hm,hR⟩ := (hq.and_eventually <| (eventually_ge_atTop N).and <| (eventually_ge_atTop d).and <| (eventually_ge_atTop m).and <| tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop R)).exists
    exact ⟨X,hX.mono hn hd hm hr hR,h⟩
  rcases frequently_or_distrib.mp hv.frequently with h|h
  · exact ⟨_,Or.inl rfl,hh _ h⟩
  exact ⟨_,Or.inr rfl,hh _ h⟩

/-- Normalize with the *specified* Maxwell comparison label for all finite Track demands on
this same hierarchy. Does not require simultaneously all jet orders on one Scaling. Very
substantial remaining hypothesis `Nonstress`, including compatible rotation-free weak
coordinate/jet comparisons. In the absence of this, `exists_stress` already works for the
conservation claim alone given two low-degree H isos. Does NOT assign the final translation
charge scale of `Spec.Locals` (further IR argument). -/
theorem stress_weak (h : G.Simple) (A : S.Hierarchy) (hW : V.Orientation A.spin) (hV : V.Derivatives S)
    (P : Lighthouse L) {τ : ℝ} (hn : τ≠0) (hJ : P.J=τ • material (Bel L) weyl) (hs : Nonstress A.spin V H P.W) :
    ∃ w : Coeff, ‖w‖ = 1 ∧ nabla V (material S w)=0 ∧ Centers (material S w) ∧ ActLaw V P (material S w) A.spin H := by
  obtain ⟨X,hX⟩ := hs 0 5 0 1 le_rfl
  obtain ⟨w,hw,h₁,h₂⟩ := exists_stress V h A hW (X.U 0 4) (X.U 0 5) (hX.path.Hsym 0 4 (by decide)) (hX.path.Hsym 0 5 (by decide))
  let J := material S w; let Q := material (Bel L) weyl
  have ht : J ∈ TableTwo A.spin := (tableStress A.spin w).property
  have hm (J : S.Stress) (Y : (Bel L).Stress) (hv : ∀ N d m R, 1 ≤ R → ∃ X, Scheme X V P.W A.spin H N d m R ∧ X.meter J Y)
      (c : ℝ) (hc : 0 < c) :
      (P.J=c • Y → ActLaw V P J A.spin H) ∧ (P.J=(-c) • Y → ActLaw V P (-J) A.spin H) := by
    have all N d m R (hr : 1 ≤ R) : ∃ X, Scheme X V P.W A.spin H N d m R ∧ X.meter J (c • Y) := by
      obtain ⟨M,hM,hl⟩ := hv N d m R hr; exact ⟨_,hM.update ..,meter_factor hl hc⟩
    constructor <;> intro hP <;> constructor <;> intro N d m R hR <;> obtain ⟨M,hM,hl⟩ := all N d m R hR
    · exact ⟨M,hM.path,hM.thick,hP ▸ hl⟩
    rw [neg_smul] at hP; exact ⟨M,hM.path,hM.thick,hP ▸ meter_neg hl⟩
  have fromPlus (h : ActLaw V P J A.spin H) : ∃ w : Coeff, ‖w‖ = 1 ∧ nabla V (material S w)=0 ∧ Centers (material S w) ∧ ActLaw V P (material S w) A.spin H :=
    ⟨w,hw,h₁,h₂,h⟩
  have fromMinus (h : ActLaw V P (-J) A.spin H) : ∃ w : Coeff, ‖w‖ = 1 ∧ nabla V (material S w)=0 ∧ Centers (material S w) ∧ ActLaw V P (material S w) A.spin H := by
    obtain ⟨h₂',-,h₁'⟩ := neg_raw V A h₂ ht h₁
    refine ⟨-w,by rwa [norm_neg],?_⟩; rw [material_neg]; exact ⟨h₁',h₂',h⟩
  obtain ⟨s, hs | hs, e⟩ := cofinal_normalization h A hV hs ht h₂ h₁ <;> rw [hs] at e <;> rcases lt_or_gt_of_ne hn with hg|hg
  · exact fromMinus ((hm J Q e (-τ) (by linarith)).2 (by simpa using hJ))
  · exact fromPlus ((hm J Q e τ hg).1 hJ)
  · exact fromPlus ((hm J (-Q) e (-τ) (by linarith)).1 (by simpa using hJ))
  exact fromMinus ((hm J (-Q) e τ hg).2 (by simpa using hJ))
end YM.StressFlux
