import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Distribution.Support
import Mathlib.MeasureTheory.Function.Floor
import YM.Euclid.RPPeak
import YM.Extraction.Orders
import YM.Mink.Poincare
import YM.Slice.Sequence
import YM.Source.Construction

/-!
# Pin finite coordinates from approximating probes (generic dimension finite)

`small/large`: physical representative outputs T using one ultracluster of
bounded *normalized* vector. Does not need sequential for mesh.fuse. Subfilter
only in proof, result exact on all tests. First-order inequality paid by
same normalization. No unbounded forest of spectators extracted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Dash
open Function Set Filter MeasureTheory Measure Complex
open scoped Topology ContDiff BigOperators
variable {V R : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
variable [NormedAddCommGroup R] [NormedSpace ℂ R] [FiniteDimensional ℂ R]
variable {S P : Type*} {ℱ : Filter S} [ℱ.NeBot]

omit [ℱ.NeBot] in
theorem fit_plane (A : S → V →ₗ[ℂ] R) (a : V →ₗ[ℂ] R) (h : ∀ i,Tendsto (fun t => A t i) ℱ (𝓝 (a i))) :
    Tendsto (fun t => LinearMap.toContinuousLinearMap (A t)) ℱ (𝓝 (LinearMap.toContinuousLinearMap a)) := by
  classical
  let b := Module.finBasis ℂ V
  let I := Fin (Module.finrank ℂ V)
  let L : (I → R) →ₗ[ℂ] V→L[ℂ] R := LinearMap.toContinuousLinearMap.toLinearMap.comp (b.constr ℂ).toLinearMap
  have he (g : V→ₗ[ℂ] R) : L (fun i => g (b i))=LinearMap.toContinuousLinearMap g := by
    apply ContinuousLinearMap.coe_injective; exact b.ext fun i => b.constr_basis ..
  have hh := L.continuous_of_finiteDimensional.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr
    (show ∀ i,Tendsto (fun t => (fun j : I => A t (b j)) i) ℱ (𝓝 ((fun j : I => a (b j)) i)) from fun i => h _))
  convert hh using 1
  · funext u; exact (he _).symm
  rw [he a]

variable (F : P → S → V →L[ℂ] ℂ) (G : P → V →L[ℂ] ℂ)


omit [FiniteDimensional ℂ V] [ℱ.NeBot] [FiniteDimensional ℂ R] in
lemma arcing {W : S → (V→L[ℂ] R)} {Y : S→ V} {X z} (hw : Tendsto W ℱ (𝓝 X)) (hy : Tendsto Y ℱ (𝓝 z)) :
    Tendsto (fun i => W i (Y i)) ℱ (𝓝 (X z)) := (show Continuous fun i : (V →L[ℂ] R) × V => i.1 i.2 from continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
  (hw.prodMk_nhds hy)

/-- Actual projection onto complement of equation-coordinate subspace.
Euclidean finite coordinates use quotient-specific norm for error.
Convergence of projectors is required from Reg . -/
structure Branch (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] (S : Type*) where
  step : S → (V→L[ℂ] V)
  trueP : V→L[ℂ] V
  projection u v : step u (step u v)= step u v
  final x : trueP (trueP x)=trueP x

def approaches (ℱ : Filter S) (p : Branch V S) := Tendsto p.step ℱ (𝓝 p.trueP)

def verified (p : Branch V S) (G : P → V →L[ℂ] ℂ) := LinearMap.ker p.trueP.toLinearMap=
    ⨅ i : P,LinearMap.ker (G i).toLinearMap

/-- Here Track `ε/(1+norm u)`. Equations tested for every spectator independently. -/
structure Added (Q : P → ℂ) (x : S → V) (p : Branch V S) (ℱ : Filter S) (F : P → S → V→L[ℂ] ℂ) : Prop where
  meets : ∀ i, Tendsto (fun u => F i u (x u)) ℱ (𝓝 (Q i))
  costly : ∀ i,Tendsto (fun u => F i u (x u-p.step u (x u)) / (1+ (↑‖p.step u (x u)‖:ℂ))) ℱ (𝓝 0)

theorem brace {p : Branch V S} (he : approaches ℱ p) (hC : verified p G) (hp : ∀ i,Tendsto (F i) ℱ (𝓝 (G i)))
    {Q : P → ℂ} (x : S → V) (h : Added Q x p ℱ F) :
    ∃ a : V, p.trueP a=a ∧ ∀ i, G i a=Q i := by
  classical
  let T (u) := p.step u (x u)
  let b u := (1+‖T u‖)⁻¹
  let z u := (↑(b u):ℂ) • T u
  have hc u : ‖z u‖=(b u)*‖T u‖ := by
    unfold z b; rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have heq u : ‖z u‖+b u=1 := by
    rw [hc]; unfold b; field_simp; ring
  have hv u : 0≤b u := by unfold b; positivity
  let α (u : S) := (b u,z u)
  have ht : ∀ᶠ u in ℱ, α u∈ (Icc 0 1 ×ˢ Metric.closedBall 0 1) := by
    apply Eventually.of_forall; intro u
    refine ⟨⟨hv _,by change b u ≤ _; linarith [heq u,norm_nonneg (z u)]⟩,?_⟩
    change dist (z u) 0 ≤ 1; rw [dist_zero_right]; linarith [heq u,hv u]
  obtain ⟨⟨c,v⟩,hs,H⟩ := (isCompact_Icc.prod (isCompact_closedBall ..)).exists_mapClusterPt_of_frequently ht.frequently
  obtain ⟨ℬ,hu,hB⟩ := mapClusterPt_iff_ultrafilter.mp H
  let Ψ : Filter S := ℬ
  have ha : Tendsto z Ψ (𝓝 v) := continuous_snd.continuousAt.tendsto.comp hB
  have hh : Tendsto b Ψ (𝓝 c) := continuous_fst.continuousAt.tendsto.comp hB
  have hL : Tendsto (fun u => (↑(b u):ℂ)) Ψ (𝓝 (c:ℂ)) := continuous_ofReal.continuousAt.tendsto.comp hh
  have hm (i) : G i v= (c:ℂ)*Q i := by
    have hb := (h.costly i).mono_left hu
    have hx : Tendsto (fun u => ((↑(b u):ℂ)*F i u (x u))- (F i u (x u-T u)/(1+(↑‖T u‖:ℂ)))) Ψ (𝓝 (c*Q i)) := by
      simpa only [sub_zero] using! (hL.mul ((h.meets i).mono_left hu)).sub hb
    refine tendsto_nhds_unique_of_eventuallyEq (arcing ((hp i).mono_left hu) ha) hx ?_
    apply Eventually.of_forall; intro j
    change F i j (z j)=_
    simp only [z,b,map_smul,smul_eq_mul, ofReal_inv,ofReal_add,ofReal_one,map_sub]; rw [div_eq_mul_inv]; ring
  have ht : p.trueP v=v := tendsto_nhds_unique_of_eventuallyEq (f:=fun i : S => p.step i (z i))
    (arcing (he.mono_left hu) ha) ha (Eventually.of_forall (fun i => by
      change p.step i (z i)=z i; rw [show z i= _ • T i from rfl,map_smul,p.projection]))
  have hj : c≠0 := by
    intro hq
    have hx : v∈LinearMap.ker p.trueP.toLinearMap := hC.symm ▸ (Submodule.mem_iInf _).2 fun i => LinearMap.mem_ker.mpr
      (show G i v=0 by rw [hm i,hq]; simp)
    have hpv : v=0 := ht.symm.trans hx
    have hr := tendsto_nhds_unique_of_eventuallyEq (ha.norm.add hh) tendsto_const_nhds (Eventually.of_forall heq)
    rw [hpv,hq] at hr
    simp at hr
  exact ⟨(c:ℂ)⁻¹ • v, by rw [map_smul,ht], fun i => by rw [map_smul,hm, smul_eq_mul, inv_mul_cancel_left₀ (by exact_mod_cast hj)]⟩
end YM.Dash
