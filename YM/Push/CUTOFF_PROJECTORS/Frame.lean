import YM.Next.EXTRACTION.Relay

/-!
# Removing equation directions in the actual (sup norm!) reference label coordinates

Here is the finite operation for --. Don't change the norm on
`C.label d` (used, amongst other places, in EXTRACTION). Embed THAT
space in a Hilbert space to do one orthogonal projection. Use the
same metric for all `(N,p)`. We take care that it is invariant under H
even though the coefficient frame need not have this property for the
standard Euclidean metric. This is a *complex* projection; the metric
respects ordinary conjugation. (No reflection included in the metric
conjugation rule.)

Every cutoff operation works, and is bounded at a cost independent even
of the subspace K being removed. No hypothesis about ranks or angles or a
positive lower bound on singular values. In particular works for empty
systems of equations. Construction of the K from finite equation matrices
on the cutoff family is in `Equations.lean`. No inference that the K's are
physical limiting nulls here!
-/

set_option autoImplicit false
noncomputable section

namespace YM.Push.CutoffProjectors
open Labels Function
open scoped BigOperators Topology InnerProductSpace

variable {G : Gauge} {d : ℕ} (F : Labels.Frame G d)

abbrev Chamber (F : Labels.Frame G d) := EuclideanSpace ℂ (Signed × F.Index)

/-- Linear H action in coefficient space at this fixed level. -/
abbrev turn (s : Signed) : F.Coeff →ₗ[ℂ] F.Coeff := F.act (Signed.inclusionO s)

@[simp] theorem turn_one (x : F.Coeff) : turn F 1 x = x := by simp [turn]

@[simp] theorem turn_mul (s r : Signed) (x : F.Coeff) :
    turn F (s*r) x = turn F s (turn F r x) := by simp [turn]

@[simp] theorem coords_bar (x : Label G d) : F.coords (realBar x) = star (F.coords x) := by
  ext1 i
  simpa only [LinearEquiv.symm_apply_apply, Pi.star_apply] using F.conj_basis (F.coords x) i

theorem turn_star (x : F.Coeff) (s : Signed) : turn F s (star x) = star (turn F s x) := by
  obtain ⟨v,rfl⟩ := F.coords.surjective x
  change F.act _ _ = star (F.act _ _)
  rw [← coords_bar, F.act_coords, F.act_coords, ← coords_bar, real_turn]

/-- Use the H orbit metric on this fixed reference frame. No normalization by
card H necessary. -/
def chart : F.Coeff →L[ℂ] Chamber F :=
  let L : F.Coeff →ₗ[ℂ] Signed × F.Index → ℂ := {
    toFun := fun x i => turn F i.1 x i.2
    map_add' := fun x y => by funext i; simp
    map_smul' := fun x y => by funext i; simp }
  ((EuclideanSpace.equiv (Signed × F.Index) ℂ).symm.toLinearEquiv.toLinearMap.comp L).toContinuousLinearMap

/-- Read the identity slice of the chart. -/
def unchart : Chamber F →L[ℂ] F.Coeff :=
  let L : (Signed × F.Index → ℂ) →ₗ[ℂ] F.Coeff := {
    toFun := fun x i => x (1,i)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  (L.comp (EuclideanSpace.equiv (Signed × F.Index) ℂ).toLinearEquiv.toLinearMap).toContinuousLinearMap

@[simp] theorem unchart_chart (x : F.Coeff) : unchart F (chart F x) = x := turn_one F x

theorem inj_chart : Injective (chart F) := (show LeftInverse (unchart F) (chart F) from unchart_chart F).injective

def pair (x y : F.Coeff) : ℂ := inner ℂ (chart F x) (chart F y)

theorem pair_formula (x y : F.Coeff) :
    pair F x y = ∑ j : Signed × F.Index, turn F j.1 y j.2 * star (turn F j.1 x j.2) :=
  EuclideanSpace.inner_eq_star_dotProduct _ _

@[simp] theorem pair_turn (s : Signed) (x y : F.Coeff) :
    pair F (turn F s x) (turn F s y) = pair F x y := by
  let e := Equiv.prodCongr (Equiv.mulRight s) (Equiv.refl F.Index)
  rw [pair_formula, pair_formula, ← e.sum_comp (fun j : Signed × F.Index =>
    turn F j.1 y j.2 * star (turn F j.1 x j.2))]
  exact Finset.sum_congr rfl fun i _ => by
    rw [← turn_mul, ← turn_mul]; rfl

@[simp] theorem pair_star (x y : F.Coeff) :
    pair F (star x) (star y) = star (pair F x y) := by
  simp only [pair_formula, turn_star, Pi.star_apply, star_star, star_sum, star_mul, mul_comm]

/-- Orthogonal complement, but in the original frame coordinates. -/
def normal (K : Submodule ℂ F.Coeff) : Submodule ℂ F.Coeff :=
  ((K.map (chart F).toLinearMap)ᗮ).comap (chart F).toLinearMap

theorem normal_iff (x : F.Coeff) (K : Submodule ℂ F.Coeff) :
    x ∈ normal F K ↔ ∀ y ∈ K, pair F y x = 0 := by
  rw [normal, Submodule.mem_comap, Submodule.mem_orthogonal]
  constructor
  · exact fun h y hy => h _ (Submodule.mem_map.mpr ⟨y,hy,rfl⟩)
  intro h v hv
  obtain ⟨u,hu,rfl⟩ := Submodule.mem_map.mp hv
  exact h u hu

/-- Projection *onto* the equation subspace. -/
def drop (K : Submodule ℂ F.Coeff) : F.Coeff →L[ℂ] F.Coeff :=
  (unchart F).comp (((K.map (chart F).toLinearMap).starProjection).comp (chart F))

/-- uses drop; the `Presentation` convention is **retain** instead. -/
def retain (K : Submodule ℂ F.Coeff) : F.Coeff →L[ℂ] F.Coeff :=
  ContinuousLinearMap.id ℂ F.Coeff - drop F K

variable (K : Submodule ℂ F.Coeff)

theorem chart_drop (x : F.Coeff) :
    chart F (drop F K x) = (K.map (chart F).toLinearMap).starProjection (chart F x) := by
  let W := K.map (chart F).toLinearMap
  obtain ⟨z,hz,h⟩ := Submodule.mem_map.mp (W.starProjection_apply_mem (chart F x))
  change chart F z = W.starProjection (chart F x) at h
  change chart F (unchart F (W.starProjection (chart F x))) = W.starProjection (chart F x)
  rw [← h, unchart_chart]

theorem chart_retain (x : F.Coeff) :
    chart F (retain F K x) = ((K.map (chart F).toLinearMap)ᗮ).starProjection (chart F x) := by
  change chart F (x - drop F K x) = _
  rw [map_sub, chart_drop, Submodule.starProjection_orthogonal_val]

@[simp] theorem drop_mem (x : F.Coeff) : drop F K x ∈ K := by
  obtain ⟨v,hv,h⟩ := Submodule.mem_map.mp ((K.map (chart F).toLinearMap).starProjection_apply_mem (chart F x))
  exact inj_chart F ((show chart F v = _ from h).trans (chart_drop F K x).symm) ▸ hv

@[simp] theorem retain_mem (x : F.Coeff) : retain F K x ∈ normal F K := by
  change chart F (retain _ _ x) ∈ (K.map (chart F).toLinearMap)ᗮ
  rw [chart_retain]; exact Submodule.starProjection_apply_mem ..

@[simp] theorem drop_fix {x : F.Coeff} : drop F K x = x ↔ x ∈ K := by
  refine ⟨fun h => h ▸ drop_mem F K x,fun h => inj_chart F ?_⟩
  rw [chart_drop, Submodule.starProjection_eq_self_iff]
  exact Submodule.mem_map.mpr ⟨x,h,rfl⟩

@[simp] theorem retain_fix {x : F.Coeff} : retain F K x = x ↔ x ∈ normal F K := by
  refine ⟨fun h => h ▸ retain_mem F K x,fun h => inj_chart F ?_⟩
  rwa [chart_retain, Submodule.starProjection_eq_self_iff]

@[simp] theorem retain_zero_iff {x : F.Coeff} : retain F K x = 0 ↔ x ∈ K := by
  change x - drop F K x = 0 ↔ _
  rw [sub_eq_zero, eq_comm, drop_fix]

@[simp] theorem retain_ker : LinearMap.ker (retain F K).toLinearMap = K :=
  Submodule.ext fun _ => retain_zero_iff F K

@[simp] theorem retain_range : LinearMap.range (retain F K).toLinearMap = normal F K := by
  ext x
  rw [LinearMap.mem_range]
  exact ⟨by rintro ⟨v,rfl⟩; exact retain_mem F K v,fun h => ⟨_,(retain_fix F K).mpr h⟩⟩

theorem removed (x : F.Coeff) : x - retain F K x ∈ K := by
  change x - (x - drop F K x) ∈ K
  rw [sub_sub_cancel]; exact drop_mem ..

theorem retain_retain (x : F.Coeff) : retain F K (retain F K x) = retain F K x :=
  (retain_fix F K).mpr (retain_mem F K x)

/-- An upper bound for *either* projection in the original sup norm.
Only depends on the level and its frame; pad to be ≥ 1. -/
def fee := (1 + ‖chart F‖) * (1 + ‖unchart F‖)
-- Def above independent of K.

theorem fee_one_le : 1 ≤ fee F := by
  unfold fee
  nlinarith [norm_nonneg (chart F), norm_nonneg (unchart F), mul_nonneg (norm_nonneg (chart F)) (norm_nonneg (unchart F))]

theorem chart_norm_le (x : F.Coeff) : ‖chart F x‖ ≤ (1+‖chart F‖) * ‖x‖ :=
  (ContinuousLinearMap.le_opNorm ..).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

theorem norm_chart (x : F.Coeff) : ‖x‖ ≤ (1+‖unchart F‖) * ‖chart F x‖ := by
  nth_rw 1 [← unchart_chart F x]
  exact (ContinuousLinearMap.le_opNorm ..).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))



theorem chart_retain_norm (x : F.Coeff) : ‖chart F (retain F K x)‖ ≤ ‖chart F x‖ := by
  rw [chart_retain]; exact Submodule.norm_starProjection_apply_le ..

theorem cost_of_contraction {L : F.Coeff →L[ℂ] F.Coeff}
    (h : ∀ x, ‖chart F (L x)‖ ≤ ‖chart F x‖) : ‖L‖ ≤ fee F := by
  refine ContinuousLinearMap.opNorm_le_bound L ((fee_one_le F).trans' zero_le_one) fun x => ?_
  have ht := norm_chart F (L x)
  rw [fee,mul_comm _ (1 + ‖unchart F‖), mul_assoc]
  exact ht.trans (mul_le_mul_of_nonneg_left ((h x).trans (chart_norm_le F x)) (by positivity))



lemma retain_le_fee : ‖retain F K‖ ≤ fee F := cost_of_contraction F (chart_retain_norm F K)



/-- Test uniqueness entirely in F's coordinates. -/
theorem eq_retain {x z : F.Coeff} (hk : z ∈ normal F K) (hz : x-z ∈ K) : retain F K x = z := by
  have hp := (retain_zero_iff F K).mpr hz
  rw [map_sub, sub_eq_zero, (retain_fix F K).mpr hk] at hp; exact hp

/-- At this cut only signed rotations. -/
def oriented := ∀ (s : Signed), ∀ x ∈ K, turn F s x ∈ K

/-- Ordinary (not OS) star. -/
def realForm := ∀ x ∈ K, star x ∈ K

lemma normal_oriented (h : oriented F K) : oriented F (normal F K) := by
  intro s x hx
  rw [normal_iff] at hx ⊢
  intro y hy
  have hp := hx _ (h s⁻¹ y hy)
  rw [← pair_turn F s] at hp
  rwa [← turn_mul, mul_inv_cancel, turn_one] at hp

lemma normal_realForm (h : realForm F K) : realForm F (normal F K) := by
  intro x hx
  rw [normal_iff] at hx ⊢
  intro y hy
  have hp := hx _ (h y hy)
  rw [← star_star y, pair_star, hp, star_zero]

theorem retain_turn (h : oriented F K) (s : Signed) (x : F.Coeff) :
    retain F K (turn F s x) = turn F s (retain F K x) :=
  eq_retain F K (normal_oriented F K h _ _ (retain_mem F K x)) (by rw [← map_sub]; exact h _ _ (removed F K x))

theorem retain_star (h : realForm F K) (x : F.Coeff) :
    retain F K (star x) = star (retain F K x) :=
  eq_retain F K (normal_realForm F K h _ (retain_mem F K x)) (by rw [← star_sub]; exact h _ (removed F K x))

section Constructor
open Next.Extract Extraction Filter

variable {C : Family G}

/-- Supply *all* finite equation subspaces from the one family. -/
abbrev Subspaces (C : Family G) := (d : ℕ) → ℕ × ℕ → Submodule ℂ (C.label d)

def present (U : Subspaces C) : Presentation C :=
  ⟨fun d i => retain (C.labels.level d) (U d i), fun d i => retain_retain _ (U d i)⟩

/-- Both stages (also for unrefined order). Costs unconditional; no spectral
hypotheses for the constructor, not even on small cutoffs. -/
theorem affordable (U : Subspaces C) (f : Order) : Affordable (present U) f := by
  have hi (d : ℕ) (v) : ‖(present U).step d v‖ ≤ fee (C.labels.level d) := retain_le_fee ..
  have hk (d : ℕ) : 0 ≤ fee (C.labels.level d) := (fee_one_le _).trans' zero_le_one
  exact ⟨fun d p => ⟨_,hk d, Eventually.of_forall (fun _ => hi _ _)⟩,
    fun d => ⟨_,hk d, Eventually.of_forall fun _ => Eventually.of_forall fun _ => hi _ _⟩⟩
end Constructor
end YM.Push.CutoffProjectors
