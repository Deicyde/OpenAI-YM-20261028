import YM.ProjectorNext.PROJECTOR_CALIBRATION.Equation

/-! # Gauge, locality and Along checks on our stencils

Advance physical applicability one step further. For every potential Campaign
using our `.weights` prove even some of the required `ComesFrom` data directly.
They need not be supplied in setting up such a Packet. No Woke or even IBP
needed to check gauge invariance of J, but include the potentially dangerous
divergence contribution (how Σ components derivative transforms, not
equality of components of course). -/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration
open Lattice Wilson RG Source Source.Drops Function Filter Labels Next.Foundations Push Push.CutoffProjectors Tensor
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
variable {G : Gauge} {H : Hol G} {d : ℕ}

lemma curve_turn (u : G.El) (v : G.Color) : G.lieExp (G.adjoint u v) = u * G.lieExp v * u⁻¹ := by
  apply G.mat_injective
  rw [G.mat_lieExp,G.mat_adjoint,G.mat_mul,G.mat_mul,G.mat_lieExp,G.exp_conjugate,G.mat_inv]; rfl

/-- Varying just e doesn't change how the tangent is conjugated at its
positive base. -/
theorem native_turn (t : Cover → G.El) (U : CoverConfig G) (e : Edge Cover) (c : G.Color) (v : ℝ) :
    pushLink (gauge t U) (Pi.single e (G.adjoint (t e.1) c)) v =
      gauge t (pushLink U (Pi.single e c) v) := by
  funext i; unfold pushLink Lattice.gauge
  by_cases h : i=e
  · subst i; simp only [Pi.single_eq_same]; rw [← map_smul,curve_turn]; group
  apply G.mat_injective
  simp [Pi.single_eq_of_ne h]

/-- Trace over physical real colors. Invariant also for a complex-valued
bilinear with neither component conjugated. -/
lemma spinbill (L : G.Color → G.Color → ℂ)
    (h1 : IsLinearMap ℝ L) (h2 : ∀ v, IsLinearMap ℝ (L v))
    (u : G.El) :
    ∑ j : G.ColorIndex, L (G.adjoint u (colors G j)) (G.adjoint u (colors G j)) =
      ∑ j : G.ColorIndex, L (colors G j) (colors G j) := by
  let Q : G.Color →ₗᵢ[ℝ] G.Color := {G.adjoint u with norm_map' := G.norm_adjoint u}
  let b := colors G
  let a (i j : G.ColorIndex) := inner ℝ (b i) (Q (b j))
  have he (i j : G.ColorIndex) : a i j = inner ℝ (G.adjoint u⁻¹ (b i)) (b j) := calc
    _ = inner ℝ (Q (G.adjoint u⁻¹ (b i))) (Q (b j)) := by rw [show Q (G.adjoint u⁻¹ (b i)) = b i by change G.adjoint u _ = _; rw [← G.adjoint_mul,mul_inv_cancel,G.adjoint_one]]
    _ = _ := Q.inner_map_map _ _
  have hh (i : G.ColorIndex) : G.adjoint u⁻¹ (b i)=∑ j,a i j • b j := by
    have hw (j : G.ColorIndex) : inner ℝ (G.adjoint u⁻¹ (b i)) (b j)=inner ℝ (b j) (G.adjoint u⁻¹ (b i)):=real_inner_comm _ _
    simp_rw [he,hw]; exact (b.sum_repr' _).symm
  have hz (i j : G.ColorIndex) : ∑ k,a i k*a j k=if i=j then 1 else 0 := by
    have hs : inner ℝ (G.adjoint u⁻¹ (b i)) (G.adjoint u⁻¹ (b j)) = inner ℝ (b i) (b j) :=
      (show G.Color →ₗᵢ[ℝ] G.Color from {G.adjoint u⁻¹ with norm_map' := G.norm_adjoint u⁻¹}).inner_map_map _ _
    nth_rw 1 [hh i] at hs
    rw [sum_inner] at hs
    have hx (k) : inner ℝ (b k) (G.adjoint u⁻¹ (b j))=a j k := by rw [he,real_inner_comm]
    simp_rw [real_inner_smul_left,hx] at hs
    rw [hs]
    simp only [b,colors,EuclideanSpace.basisFun_inner]; rw [EuclideanSpace.basisFun_apply]; by_cases h : i=j <;> simp [h]
  let P := IsLinearMap.mk' _ h1
  let R (x : G.Color) := IsLinearMap.mk' _ (h2 x)
  have hv (j : G.ColorIndex) : L (Q (b j)) (Q (b j)) = ∑ i, ∑ l, (a i j*a l j) • L (b i) (b l) := by
    have hk : Q (b j)=∑ i,a i j • b i := (b.sum_repr' _).symm
    nth_rw 1 [hk]
    change P _ _ = _; rw [_root_.map_sum,Finset.sum_apply]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul,Pi.smul_apply]
    change a i j • R (b i) _ = _; rw [hk,_root_.map_sum,Finset.smul_sum]; simp_rw [map_smul,smul_smul]; rfl
  change ∑ j, L (Q (b j)) (Q (b j)) = _
  simp_rw [hv]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]; simp_rw [← Finset.sum_smul, hz]; simp [b,ite_smul]

namespace Machine
variable (M : Machine H d) (F : Labels.Frame G d)

/-- Conjugating weights and derivative directions together is needed to use
the unweighted Haar divergence. -/
lemma invariant_div (m : F.Index) : GaugeInvariant (M.divLeg F m) := by
  intro t U
  let L (V : CoverConfig G) (i : M.Outlet) (a b : G.Color) := left (M.valve F m i a) (M.address i) b V
  change (∑ i, ∑ j,L (gauge t U) i (colors G j) (colors G j)) = ∑ i, ∑ j,L U i (colors G j) (colors G j)
  refine Finset.sum_congr rfl fun i _ => ?_
  let u := t (M.address i).1
  have ht (a b : G.Color) : L (gauge t U) i (G.adjoint u a) (G.adjoint u b) = L U i a b := by
    unfold L left; apply congr_arg (fun f : ℝ → ℂ => deriv f 0); funext v
    rw [native_turn t U (M.address i) b v,M.valve_gauge]
  have hh (V : CoverConfig G) (a b : G.Color) : HasDerivAt (fun z => M.valve F m i a (pushLink V (Pi.single (M.address i) b) z)) (L V i a b) 0 := by
    obtain ⟨s,h⟩ := M.small_valve F m i a; exact h.authentic _ _ _
  have h₁ (V : CoverConfig G) : IsLinearMap ℝ (L V i) := by
    constructor
    · intro a b; funext c; change deriv _ _ = L V i a c + L V i b c
      simp_rw [← M.valveL_apply,map_add,M.valveL_apply]; exact ((hh V a c).add (hh V b c)).deriv
    intro a b; funext c; change deriv _ _ = a • L V i b c
    simp_rw [← M.valveL_apply,map_smul,M.valveL_apply]; exact ((hh V b c).const_smul a).deriv
  have h₂ (V : CoverConfig G) (a : G.Color) : IsLinearMap ℝ (L V i a) := by
    obtain ⟨s,h⟩ := M.small_valve F m i a; exact h.linear _ _
  rw [← spinbill _ (h₁ _) (h₂ _) u]; exact Finset.sum_congr rfl fun j _ => ht ..

lemma invariant_energy (m : F.Index) : GaugeInvariant (M.energyLeg F m) := by
  intro t U
  unfold energyLeg; simp_rw [gradient_gauge,M.valve_gauge]

variable {C : Family G} (M₀ : Machine C.params d) {N p : ℕ} (E : Packet C d N p)

section Auth
variable {s : Finset Cover} (he : M₀.Release s) (hs : Machine.Opened s (C.side N p)) (ht : M₀.lined E)
include he hs ht

lemma colored_J (x : equationSpace (C.labels.level d)) : GaugeInvariant (E.Jorigin x) := by
  intro t U
  refine mul_left_cancel₀ (b:=(_ : ℂ)) (c:= _) (pow_ne_zero d (Complex.ofReal_ne_zero.mpr (C.S.a_pos N).ne')) ?_
  simp_rw [M₀.undressed E he hs ht,expandAt_gauge]
  let F := C.labels.level d
  exact Finset.sum_congr rfl fun i _ => by rw [M₀.invariant_energy F i,M₀.invariant_div F i]

lemma supported_J (x : equationSpace (C.labels.level d)) : LocalOn (Packet.sites (C.side N p) s) (E.Jorigin x) := by
  intro U V h
  refine mul_left_cancel₀ (b:=(_ : ℂ)) (c:= _) (pow_ne_zero d (Complex.ofReal_ne_zero.mpr (C.S.a_pos N).ne')) ?_
  simp_rw [M₀.undressed E he hs ht]
  have hx (f : CoverConfig G → ℂ) (hg : LocalOn s f) : f (expandAt 0 U)=f (expandAt 0 V) := by
    apply hg; intro e he hf
    unfold expandAt; simp only [add_zero]
    refine h _ (Finset.mem_image.mpr ⟨_,he,rfl⟩) (Finset.mem_image.mpr ⟨_,hf,?_⟩); simp
  exact Finset.sum_congr rfl fun i _ => by rw [hx (M₀.energyLeg (C.labels.level d) i) (M₀.release_energy _ he i).supported,hx (M₀.divLeg (C.labels.level d) i) (M₀.release_div _ he i).supported]

end Auth

end Machine
end YM.ProjectorNext.Calibration
