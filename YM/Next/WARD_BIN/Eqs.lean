import YM.Next.WARD_BIN.Triangular

/-!
# Basis on the equation ideal

Actual ideal on *real* Lie coordinates complexified, not a new kernel. Build
one real pure-grade basis. H-equivariant choices of equation cylinders aren't
needed for our use (we separately transport the literal cylinders with every
symmetry in the reflection estimates). No H assertion on the choices here!
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Set Filter MeasureTheory Wilson Lattice RG Source Source.Drops Labels Work.G05 Bid Maxwell
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {d l n : ℕ} {H : Hol G}

private lemma tests_pow (c : ℕ → ℕ → ℂ) (hc : ∀ t s : ℝ, (∑ i∈ Finset.range (d+1), ∑ j∈ Finset.range (d+1), t^i • s^j • c i j) = 0)
    (hi : n ≤ d) (hl : l ≤ d) : c n l=0 := by
  let B := Finset.range (d+1)
  have hx (i : ℕ) (hi : i≤d) (p : ℕ→ℂ) (hp : ∀ t : ℝ,(∑ j∈B,t^j • p j)=0) : p i=0 := by
    have h : leading i (fun t : ℝ => ∑ j ∈ B,t^j • p j)=0 := by simp_rw [hp];simp [leading]
    rw [lead_sum _ (f:=fun j (t:ℝ) => t^j • p j) (by intros; exact (monoSmooth ..).contDiffAt)] at h
    simpa only [lead_monomial,Finset.sum_ite_eq, B, Finset.mem_range.mpr (Nat.lt_succ_of_le hi),↓reduceIte] using h
  refine hx _ hl _ fun t => ?_
  apply hx _ hi (fun k => ∑ j∈B,t^j • c k j)
  intro s; simp_rw [Finset.smul_sum]; exact hc s t

lemma equationPart {p : Label G d} (hp : p∈equationIdeal G d) (hn : n ≤ d) (hl : l ≤ d) :
    gradePart (n,l) p∈equationIdeal G d := by
  apply ideal_meaning.mpr; intro X
  let A : Jet G := fun j => gaugeJet (X j)
  apply tests_pow (d:=d) (fun i k => Labels.read A (gradePart (i,k) p).val) _ hn hl
  intro t s
  let Y : TaylorTower G := fun i => t^(i+2) • s • X i
  have he : scaleJet (s • A) t = (fun i => gaugeJet (Y i)) := by
    funext i; change t^(i+2) • s • gaugeJet _ = gaugeJet (t^_ • s • _); rw [map_smul,map_smul]
  have hv := ((ideal_meaning (A:=p)).mp hp Y)
  rw [← he, show p.val=(∑ i∈ Finset.range (d+1), ∑ j∈ Finset.range (d+1), gradePart (i,j) p).val from congr_arg (fun a:Label G d => a.val) (decompose p).symm] at hv
  simp only [AddSubmonoidClass.coe_finsetSum, map_sum] at hv
  have hh (i k) : Labels.read (scaleJet (s • A) t) (gradePart (i,k) p).val=
      t^i • s^k • Labels.read A (gradePart (i,k) p).val := by
    rw [scaled_grade t _ _ (gradePart_mem ..),multiplied_grade s _ _ (gradePart_mem ..)]
  -- subtype tower might include diff smul-instance but evaluations here fixed
  simp_rw [hh] at hv; exact hv

lemma equationBar {p : Label G d} (hp : p∈equationIdeal G d) : realBar p∈equationIdeal G d := by
  apply ideal_meaning.mpr; intro X
  change Labels.read _ (conjPol p.val) = _
  rw [conj_value, ideal_meaning.mp hp X]; simp

lemma equationUnit : Labels.unit G d ∉ equationIdeal G d := by
  intro h; have ht := ideal_meaning.mp h 0
  change Labels.read _ 1=0 at ht; simp at ht

-- choose spanning by grade after restricting with hp!
private def forBasis (G : Gauge) (d : ℕ) := {v : (equationIdeal G d) | realBar v.val=v.val ∧
    ∃ (l n : ℕ), l+1≤d ∧ n≤d ∧ v.val ∈ Grade (n,l+1) }

private lemma equationSpan (G : Gauge) (d) : ⊤ ≤ Submodule.span ℂ (forBasis G d) := by
  classical
  intro x _
  let S := Submodule.span ℂ (forBasis G d)
  have ht (y : equationIdeal G d) (i j : ℕ) (hi : i≤d) (hj : j≤ d) (he : y.val∈ Grade (i,j)) : y ∈ S := by
    cases j with
    | zero =>
      suffices y=0 by rw [this]; exact S.zero_mem
      obtain ⟨r,hr⟩ := scalar_grade (v:=y.val) i he
      have hu : r=0 := by
        by_contra h
        have hx : r⁻¹ • (r • Labels.unit G d) ∈ equationIdeal G d :=
          (equationIdeal G d).smul_mem _ (hr ▸ y.property)
        rw [inv_smul_smul₀ h] at hx; exact equationUnit hx
      apply Subtype.ext; rw [hr,hu,zero_smul]; rfl
    | succ j =>
      let z : equationIdeal G d := ⟨_, equationBar y.property⟩
      have hh : z.val ∈ Grade (G:=G) (i,j+1) := by
        have hm := gradePart_bar (i,j+1) y.val; rw [gradePart_self y.val _ he] at hm
        change realBar y.val ∈ _; rw [← hm]; exact gradePart_mem _ _
      have hu : y+z ∈ S := Submodule.subset_span (show _∈forBasis G d from
        ⟨by change realBar (y.val+realBar y.val) = _; rw [map_add,twice,add_comm]; rfl, j,i,hj,hi,Submodule.add_mem _ he hh⟩)
      have hv : Complex.I • (y-z) ∈ S := Submodule.subset_span (show _∈forBasis G d from
        ⟨by change realBar (Complex.I • (y.val-realBar y.val))=_; rw [realBar.map_smulₛₗ,map_sub,twice]; simp [z, smul_sub]; abel,
          j,i,hj,hi,Submodule.smul_mem _ Complex.I (Submodule.sub_mem _ he hh)⟩)
      have hw := S.smul_mem (1/2:ℂ) (S.add_mem hu (S.smul_mem (-Complex.I) hv))
      rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg,one_smul, show y+z+(y-z)= (2:ℂ) • y by rw [two_smul]; abel,
        smul_smul,div_mul_cancel₀ _ (by norm_num),one_smul] at hw
      exact hw
  let B (i j : ℕ) : equationIdeal G d := if h : i≤d ∧ j≤d then
    ⟨_, equationPart x.property h.1 h.2⟩ else 0
  have hb (i j : ℕ) (hi : i≤d) (hj : j≤d) : (B i j).val=gradePart (i,j) x.val := by unfold B; rw [dif_pos ⟨hi,hj⟩]
  let v := ∑ i∈ Finset.range (d+1),∑ j∈ Finset.range (d+1), B i j
  have hw : v=x := Subtype.ext (Eq.trans ?_ (decompose x.val))
  · suffices hv : v∈ S by simpa only [hw] using hv
    refine Submodule.sum_mem _ (fun i hi => Submodule.sum_mem _ (fun j hj => ?_))
    simp only [Finset.mem_range,Nat.lt_succ_iff] at hi hj
    refine ht _ i j hi hj ?_; rw [hb i j hi hj]; exact gradePart_mem _ _
  unfold v; simp only [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => ?_))
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hi hj; exact hb i j hi hj

abbrev Count (G : Gauge) (d : ℕ) := Fin (Module.finrank ℂ (equationIdeal G d))

structure PureBasis (G : Gauge) (d : ℕ) where
  basis : Module.Basis (Count G d) ℂ (equationIdeal G d)
  s (i : Count G d) : ℕ -- degree minus one (no degree zero in the equation ideal)
  n (i : Count G d) : ℕ
  le i : s i+1≤d
  degree i : n i≤d
  realForm i : realBar (basis i).val = (basis i).val
  homogeneous i : (basis i).val ∈ Grade (n i,s i+1)

lemma basisEq (G : Gauge) (d : ℕ) : Nonempty (PureBasis G d) := by
  classical
  obtain ⟨S,hS,-,hp,h⟩ := exists_linearIndepOn_id_extension (linearIndepOn_empty ℂ id)
    (empty_subset (forBasis G d))
  have hv := (equationSpan G d).trans (Submodule.span_le.mpr hp)
  let b := Module.Basis.mk (show LinearIndependent ℂ (Subtype.val : S → _) from h.linearIndependent_restrict)
    (show ⊤ ≤ Submodule.span ℂ (range (Subtype.val : S → _)) by simpa using hv)
  haveI : Finite S := Module.Finite.finite_basis b
  letI := Fintype.ofFinite S
  let V := (Fintype.equivFin S).trans (finCongr (Module.finrank_eq_card_basis b).symm)
  let B := b.reindex V
  have ht (i) : B i ∈ forBasis G d := hS (by rw [show B i=(V.symm i).val by simp [B,b]]; exact (V.symm i).property)
  choose l n hL hN hh using fun i => (ht i).2
  exact ⟨⟨B,l,n,hL,hN,fun i => (ht i).1,hh⟩⟩
namespace PureBasis
variable (B : PureBasis G d)

def form (i : Count G d) := toTensor (B.s i+1) (B.basis i).val

lemma truth (i : Count G d) : Rays.covariantTensor (B.form i) := tensor_eqv (B.homogeneous i)





variable (R : Rays G d H)



end PureBasis
end YM.WardBin
