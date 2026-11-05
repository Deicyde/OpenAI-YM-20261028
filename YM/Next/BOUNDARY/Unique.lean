import Mathlib.Analysis.ODE.ExistUnique
import YM.Work.A16




/-!
# Choice interfaces at the boundary

Uniqueness where meaningful! No identification of S with a selected phase;
compare two constructions over the **same** hierarchy T and common label
system S. Don't compare the values stored outside the open set of strict
times. In particular `Opens`, although asking only for fixed-slope limits,
pins the entire joint `Surface` (all arities, all Schwartz tests).

Use the same one-parameter trick as in Work.C22 for complex times, and
constant-coefficient ODE idea as Work.A17 for boosts. Also the Fourier
emissions and all closed-cone partial boundaries are independent of the
auxiliary frequency blankets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.BOUNDARY

open Set Filter Function MeasureTheory
open YM.Boundary
open scoped Topology InnerProductSpace

variable {G : Gauge} {L : Register G} {S T : Table L}

open Complex in
/-- Identity theorem with data on the purely imaginary slice. Holds also
for n=0. (Time is the final coordinate in `Points`; here only `Times`.) -/
theorem ordered_eq {n : ℕ} (f g : Times n → ℂ)
    (hf : DifferentiableOn ℂ f (strict n)) (hg : DifferentiableOn ℂ g (strict n))
    (h : ∀ y ∈ east n, f (fun i => (y i:ℂ)*I) = g (fun i => (y i:ℂ)*I)) :
    EqOn f g (strict n) := by
  intro z hz
  let Z (c : ℂ) : Times n := fun i => ((z i).im:ℂ)*I+c*((z i).re:ℂ)
  let y (t : ℝ) : Heights n := fun i => (z i).im+t*(z i).re
  have hZ (c : ℂ) : (fun i => (Z c i).im)=y c.im := by
    funext i
    simp [Z, y]
  have hy0 : y 0∈east n := by
    rw [show y 0=(fun i => (z i).im) by funext i; simp [y]]
    exact hz
  have hy : Continuous y := by unfold y; fun_prop
  obtain ⟨r, hr, hδ⟩ := Metric.eventually_nhds_iff.mp
    ((hy.tendsto 0).eventually ((open_east n).mem_nhds hy0))
  let U := im ⁻¹' Ioo (-r) r
  have hu : IsOpen U := isOpen_Ioo.preimage continuous_im
  have hc : IsPreconnected U := ((convex_Ioo (-r) r).linear_preimage imCLM.toLinearMap).isPreconnected
  have hρ (t : ℝ) (ht : -r<t ∧ t<r) : y t∈east n := hδ (by simpa [Real.dist_eq, abs_lt] using ht)
  have ht : MapsTo Z U (strict n) := by
    intro c hU
    change (fun i => (Z c i).im) ∈ east n
    rw [hZ]
    exact hρ _ hU
  have hZD : Differentiable ℂ Z := by unfold Z; fun_prop
  have hstart : (0:ℂ)∈U := ⟨neg_lt_zero.mpr hr, hr⟩
  have heq : EqOn (f ∘ Z) (g ∘ Z) U := by
    refine ((hf.comp hZD.differentiableOn ht).analyticOnNhd hu).eqOn_of_preconnected_of_frequently_eq
      ((hg.comp hZD.differentiableOn ht).analyticOnNhd hu) hc hstart ?_
    intro hn
    let w (t : ℝ) := (t:ℂ)*I
    have hw : Tendsto w (𝓝[>] (0:ℝ)) (𝓝[≠] (0:ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have hi : Continuous w := continuous_ofReal.mul continuous_const
        simpa [w] using ((hi.tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Ioi 0)))
      filter_upwards [self_mem_nhdsWithin] with i hi
      change w i ≠ 0
      simp [w, (mem_Ioi.mp hi).ne']
    obtain ⟨t, hn, hw⟩ := ((hw.eventually hn).and
      ((hw.mono_right nhdsWithin_le_nhds).eventually (hu.mem_nhds hstart))).exists
    apply hn
    change f (Z (w t))=g (Z (w t))
    have hp : Z (w t) = fun i => (y t i:ℂ)*I := by
      funext i
      dsimp [Z, w, y]; push_cast; ring
    change -r < (w t).im ∧ (w t).im < r at hw
    rw [hp]
    exact h (y t) (hρ _ (by simpa [w] using hw))
  have h1 := heq (show (1:ℂ)∈U from ⟨neg_lt_zero.mpr hr, hr⟩)
  have hz1 : Z 1=z := by
    funext i
    simp [Z, add_comm]
  simpa only [Function.comp_apply, hz1] using h1

/-- At all strict times and real spatial arguments, on the genuine common
label system. Independent of the choice of analytic producer. -/
theorem waves_eq {Y Z : Waves S} (hY : Y.Region T) (hZ : Z.Region T)
    (P : DiffPlan S) (hS : S.Symmetric) (hP : P.Inclusions S) (n : ℕ) (x : SpacePoints n)
    (z : Times n) (hz : z ∈ strict n) : Y.F n z x = Z.F n z x := by
  ext1 v
  apply ordered_eq _ _ (hY.hol n v x) (hZ.hol n v x) _ hz
  obtain ⟨d, w, rfl⟩ := P.joint hS hP v
  intro y hy
  let a : Fin n → S.Tag := fun i => ⟨d, w i⟩
  exact (hY.roots n a x y hy).trans (hZ.roots n a x y hy).symm

theorem surface_eq {Y Z : Contour S} (hY : Y.From T) (hZ : Z.From T)
    (P : DiffPlan S) (hS : S.Symmetric) (hP : P.Inclusions S) :
    Y.world = Z.world := by
  have e : Y.world.W = Z.world.W := by
    funext n
    ext1 v
    ext1 f
    let y : Heights n := rate n
    have hy : y ∈ east n := fun i j hij => by
      unfold y rate; exact_mod_cast hij
    refine tendsto_nhds_unique_of_eventuallyEq (hY.emerges.profile n v y hy f)
      (hZ.emerges.profile n v y hy f) ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    unfold Waves.atSlopes
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only [Waves.restricted]
    rw [waves_eq hY.heat hZ.heat P hS hP _ _ _ (on_profile _ _ _ hε hy)]
  have h (A B : Surface S) (e : A.W=B.W) : A=B := by
    cases A
    cases B
    congr
  exact h _ _ e

section generators
variable {R : S.Rotation} {h : S.RealSpin} {K M : Spins S}
open Mink

private theorem one (hK : K.Descends R h) (d : ℕ) (v : S.Field d) : K.shell d 1 v=v :=
  S.pin_inj _ ((hK.ties 1 d v).symm.trans (hK.identity _))

private theorem mult (hK : K.Descends R h) (d : ℕ) (a b : Lorentz) (v : S.Field d) :
    K.shell d (a*b) v=K.shell d a (K.shell d b v) := by
  apply S.pin_inj
  simpa only [hK.ties] using hK.representation a b (S.pin d v)

private theorem shell_boost_eq (hK : K.Descends R h) (hM : M.Descends R h) (d : ℕ)
    (a : SpaceAxis) (r : ℝ) (v : S.Field d) :
    K.shell d ((Ray.fromAxis a).boost r) v = M.shell d ((Ray.fromAxis a).boost r) v := by
  let N := LinearMap.toContinuousLinearMap ((-Complex.I) • R.lie d (Ortho.plane timeAxis a.castSucc))
  let f (B : Spins S) := fun t => B.shell d ((Ray.fromAxis a).boost t) v
  have hf (B : Spins S) (hB : B.Descends R h) (t : ℝ) : HasDerivAt (f B) (N (f B t)) t := by
    have hd := hB.boosts d a (f B t)
    simpa only [f, Function.comp_def, one_smul, ← mult hB, ← Ray.boost_add, sub_add_cancel] using!
      hd.scomp_of_eq t ((hasDerivAt_id' t).sub_const t) (by simp)
  have he : f K 0 = f M 0 := by simp [f, one hM, one hK]
  exact congr_fun (ODE_solution_unique_univ (s:=fun _ => univ)
    (fun (_ : ℝ) => N.lipschitz.lipschitzOnWith) (fun t => ⟨hf K hK t, mem_univ _⟩)
    (fun t => ⟨hf M hM t, mem_univ _⟩) he) r

/-- Use of two (perhaps independently obtained) Lorentz witnesses with the
same Euclidean rotation data. -/
theorem spins_eq (hK : K.Descends R h) (hM : M.Descends R h) (P : DiffPlan S)
    (hs : S.Symmetric) (hP : P.Inclusions S) : K=M := by
  have hf (d : ℕ) (b : Lorentz) : ∀ v : S.Field d, K.shell d b v=M.shell d b v := by
    have hp : b∈Bid.beamGens := by rw [(Work.A16.answer : Bid.beamGens=⊤)]; trivial
    exact Subgroup.closure_induction (p := fun b _ => ∀ v : S.Field d, K.shell d b v=M.shell d b v)
      (by
        intro b hb v
        rcases hb with ⟨s, t, rfl⟩ | ⟨a, u, rfl⟩
        · rw [hK.spatial s t, hM.spatial s t]
        exact shell_boost_eq hK hM d a u v)
      (fun v => (one hK d v).trans (one hM d v).symm)
      (by intro a b _ _ ha hb v; simp only [mult hK, mult hM, hb, ha])
      (by
        intro a _ ha v
        apply (M.shell d a).injective
        rw [← ha, ← mult hK, ← mult hM, mul_inv_cancel, one hK, one hM]) hp
  have hx : K.rail=M.rail := by
    funext b
    ext1 v
    obtain ⟨d, w, rfl⟩ := P.covered hs hP v
    simp only [hK.ties, hM.ties, hf]
  have he : K.shell=M.shell := by funext d b; ext1 v; exact hf d b v
  cases K
  cases M
  congr


end generators

section tube
open Distribution
variable {n : ℕ}



theorem emit_eq (W : Surface S) (v : Fin n → S.Union)
    (h : dsupport (Distn.fourier (W.W n v)) ⊆ coneM n)
    {A B : ∀ i : ℕ, Blanket i} (F : W.Aurora A) (J : W.Aurora B)
    (x : Full n) (hx : x∈tube n) : F.emit v x = J.emit v x := by
  unfold Surface.Aurora.emit
  congr 1
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (Distn.due _ _ (closedM _)).1 h
  intro p ht hp
  have HH : Disjoint (Metric.ball p 1) (Function.support (F.lens n x - J.lens n x)) := by
    refine Set.disjoint_left.mpr fun z hz H => H ?_
    change F.lens n x z - J.lens n x z = 0
    have hw : z∈ShadeSet 1 n := ⟨p, hp, hz⟩
    rw [F.shape n x hx, J.shape n x hx]
    simp [Blanket.lens, Blanket.attenuate, (A n).immediate _ hw, (B n).immediate _ hw]
  exact Set.disjoint_left.1 (HH.closure_right Metric.isOpen_ball) (Metric.mem_ball_self zero_lt_one) ht
end tube
end YM.Next.BOUNDARY
