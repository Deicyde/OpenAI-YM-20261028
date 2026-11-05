import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.ODE.ExistUnique
import YM.Analysis.Polydisc
import YM.Next.MAXWELL.Ends
import YM.Pressure.Seeds


/-!
# Jet-order support and length gradings

Shelf j: uses only jet orders ≤j. lowerCap uses weights. Also use
finite-support lengths, never take a uniform-length assumption.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open MvPolynomial hiding monomial
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge} {j k w m n : ℕ}

abbrev Rack (G : Gauge) (j : ℕ) := MvPolynomial.supported (σ:=Slot G) ℂ {i| i.1≤j}
abbrev shelf (G : Gauge) (j : ℕ) := (Rack G j).toSubmodule

abbrev gloss {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : M) := MvPolynomial.weightedHomogeneousComponent (R:=ℂ) (fun s : Slot G => f s.1) k
abbrev distill (k : ℕ) := gloss (G:=G) (fun _ => (1:ℕ)) k
abbrev bulk (p : Slot G →₀ ℕ) := Finsupp.weight (fun _ : Slot G => (1:ℕ)) p
abbrev Pure (k : ℕ) (p : WickPol G) := IsWeightedHomogeneous (fun _ => (1:ℕ)) p k

lemma gloss_mirror {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : M) (s : Ortho) (p : WickPol G) : gloss f k (reflectPol s p)=reflectPol s (gloss f k p) := by
  apply commuting (fun i : Slot G => f i.1) _ _ _ p k
  intro i; rw [reflectPol,MvPolynomial.aeval_X]; exact symbol_hom _ _

lemma gloss_pigment {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : M) (u : G.El) (p : WickPol G) : gloss f k (pigment u p) = pigment u (gloss f k p) := by
  apply commuting (fun i : Slot G => f i.1) _ _ _ p k
  intro i; rw [pigment,MvPolynomial.aeval_X]; exact symbol_hom _ _
lemma painted_gloss {M : Type*} [AddCommMonoid M] (f : ℕ→ M) (k : M) {p : WickPol G} (h : Painted p) : Painted (gloss f k p) := by
  intro u; rw [← gloss_pigment,h u]
lemma real_gloss {M : Type*} [AddCommMonoid M] (f : ℕ→ M) (k : M) (p : WickPol G) : gloss f k (realForm p) = realForm (gloss f k p) := by
  classical
  ext i; simp only [gloss,realForm,coeff_weightedHomogeneousComponent,MvPolynomial.coeff_map]; split <;> simp
lemma moyenne_gloss {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : M) (p : WickPol G) : gloss f k (moyenne G p)=moyenne G (gloss f k p) := by
  apply equalPol; intro A
  let L := (probe A).toLinearMap
  let B := gloss (G:=G) f k
  rw [show probe A _=(L.comp B) (moyenne G p) from rfl,blended,show probe A (moyenne G _) = L (moyenne G _) from rfl, blended]; unfold B; simp only [LinearMap.comp_apply,gloss_pigment]

lemma colors_grade {M : Type*} [AddCommMonoid M] (f : ℕ→ M) (k : M) {p : WickPol G} (h : p∈ shellSector G j) : gloss f k p∈ shellSector G j := by
  classical
  obtain ⟨A,H⟩ := sector.mp h; rw [lowerCap, MvPolynomial.mem_restrictSupport_iff] at A
  refine sector.mpr ⟨?_,painted_gloss _ _ H⟩
  rw [lowerCap,MvPolynomial.mem_restrictSupport_iff]; intro x hx; apply A
  rw [Finset.mem_coe,MvPolynomial.mem_support_iff] at hx ⊢; rw [gloss,coeff_weightedHomogeneousComponent] at hx
  split at hx
  · exact hx
  contradiction

lemma shelf_support {p : WickPol G} : p ∈ shelf G j ↔ ∀ u : Slot G →₀ ℕ,p.coeff u≠0 → ∀ i∈u.support, i.1≤j := by
  rw [Subalgebra.mem_toSubmodule,MvPolynomial.mem_supported]
  constructor
  · intro h u hu i hi; exact h ((mem_vars_iff_mem_support i).mpr ⟨u,MvPolynomial.mem_support_iff.mpr hu,hi⟩)
  intro h i hi; obtain ⟨u,hu,hp⟩ := (mem_vars_iff_mem_support i).mp hi; exact h u (MvPolynomial.mem_support_iff.mp hu) i hp

lemma single_le {σ : Type*} {i : σ} {p : σ →₀ ℕ} (hp : i ∈ p.support) : Finsupp.single i 1 ≤ p := by
  classical
  intro j; by_cases he : j=i
  · subst j; rw [Finsupp.single_eq_same]; exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  simp [Ne.symm he]

lemma deg_down {p : Slot G →₀ ℕ} {i : Slot G} (hp : i ∈ p.support) : degree (p-Finsupp.single i 1)+(i.1+2)=degree p := by
  have he := weight_next (p-Finsupp.single i 1) i
  rw [tsub_add_cancel_of_le (single_le hp)] at he; omega

lemma cap_shelf (p : WickPol G) (hp : p ∈ lowerCap G w) : p∈ shelf G w := by
  rw [lowerCap, MvPolynomial.mem_restrictSupport_iff] at hp
  rw [shelf_support]; intro u h i hi
  have ht : degree u ≤ w := hp (MvPolynomial.mem_support_iff.mpr h); have he := deg_down hi; omega

lemma gloss_shelf {M : Type*} [AddCommMonoid M] (f : ℕ→ M) (k : M) (p : WickPol G) (hp : p ∈ shelf G j) : gloss f k p∈ shelf G j := by
  classical
  rw [shelf_support]; intro u h i hi; rw [gloss,coeff_weightedHomogeneousComponent] at h; split at h
  · exact shelf_support.mp hp _ h i hi
  contradiction
lemma symbol_shelf (p : Probe G j) {l : ℕ} (h : j≤l) : symbol j p∈ shelf G l := by
  unfold symbol; apply Submodule.sum_mem; intro i _
  rw [C_mul']; exact Submodule.smul_mem _ _ (show X (R:=ℂ) _∈Rack G l from X_mem_supported.mpr h)
lemma spaced_mirror (s : Ortho) {p : WickPol G} (h : p∈shelf G j) : reflectPol s p∈shelf G j := by
  let V := (Rack G j).comap (reflectPol s)
  suffices hv : Rack G j ≤ V from hv h
  rw [Rack,supported, Algebra.adjoin_le_iff]; rintro v ⟨i,hi,rfl⟩
  change reflectPol s (X (R:=ℂ) i)∈shelf G j; rw [reflectPol,aeval_X]; exact symbol_shelf _ hi
lemma spaced_pigment (s : G.El) {p : WickPol G} (h : p∈shelf G j) : pigment s p∈shelf G j := by
  let V := (Rack G j).comap (pigment s)
  suffices hv : Rack G j ≤ V from hv h
  rw [Rack,supported,Algebra.adjoin_le_iff]; rintro v ⟨i,hi,rfl⟩
  change pigment s (X (R:=ℂ) i)∈shelf G j
  rw [pigment,MvPolynomial.aeval_X]; exact symbol_shelf _ hi
lemma spaced_real {p : WickPol G} (h : p∈shelf G j) : realForm p∈shelf G j := by
  rw [shelf_support]; intro x hx; rw [realForm,MvPolynomial.coeff_map] at hx
  exact shelf_support.mp h _ (fun ha => hx (by rw [ha,map_zero]))
lemma spaced_moy (p : WickPol G) (h : p∈ shelf G j) : moyenne G p∈ shelf G j := by
  apply shelf_support.mpr; intro u hx i hi
  by_contra H
  have hm s : (pigment s p).coeff u=0 := by
    by_contra ht; exact H (shelf_support.mp (spaced_pigment s h) u ht i hi)
  apply hx
  let f := (MvPolynomial.coeff (σ := Slot G) (R := ℂ) u)
  -- define linear eval
  let L : WickPol G →ₗ[ℂ] ℂ := { toFun := fun p => MvPolynomial.coeff u p, map_add' _ _ := MvPolynomial.coeff_add u _ _, map_smul' _ _ := MvPolynomial.coeff_smul .. }
  change L (moyenne G p)=_; rw [blended]; change (∫ s,(pigment s p).coeff u ∂G.probHaar)=0; simp [hm]

lemma distilled_eq (k : ℕ) (p : WickPol G) : Pure k p ↔ distill k p=p := by
  constructor
  · intro h; exact h.weightedHomogeneousComponent_same
  intro h; rw [← h]; exact weightedHomogeneousComponent_isWeightedHomogeneous k p
lemma bulk_zero (p : WickPol G) (hp : Pure 0 p) : p=C (p.coeff 0) := by
  classical
  ext s; rw [MvPolynomial.coeff_C]; split_ifs with h
  · subst s; rfl
  by_contra hv
  obtain ⟨i,hi⟩ : s.support.Nonempty := by simpa [eq_comm] using h
  have he : bulk (s - Finsupp.single i 1 + Finsupp.single i 1)=bulk s := by rw [tsub_add_cancel_of_le (single_le hi)]
  have hh : bulk s=0 := hp hv
  rw [hh] at he; simp [bulk,Finsupp.weight_single] at he

lemma pure_mirror (s : Ortho) (p : WickPol G) (hp : Pure k p) : Pure k (reflectPol s p) :=
  (distilled_eq ..).mpr ((gloss_mirror _ k s p).trans (congr_arg _ ((distilled_eq ..).mp hp)))
lemma pure_real (p : WickPol G) (hp : Pure k p) : Pure k (realForm p) :=
  (distilled_eq ..).mpr ((real_gloss _ k p).trans (congr_arg _ ((distilled_eq ..).mp hp)))

lemma cap_exists (p : WickPol G) : ∃ d, p∈lowerCap G d := by
  classical
  refine ⟨p.weightedTotalDegree scaleW,?_⟩; rw [lowerCap, MvPolynomial.mem_restrictSupport_iff]; intro i hi
  exact Finset.le_sup (f:=Finsupp.weight scaleW) hi
end YM.Maxwell.Free
