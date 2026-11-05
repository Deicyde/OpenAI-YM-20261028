import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.PSeries
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import YM.Next.BOUNDARY.Coordinates
import YM.Next.SCHEDULE.Dues
import YM.Push.BETA_TRANSPORT.Comparisons
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.PRICE_COMPILER.Post
import YM.UVNext.FREE_STRESS_CERTIFICATE.Diagonal

/-! Count ranks at and below 4, with basis response data. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Labels Climb Table Work.A01 Next.UVStress Function Set Submodule MvPolynomial
variable {G : Gauge} (F : Frames G) {d : ℕ} (hG : G.Simple)

private lemma not_thin {P : Pol G} (H : IsWeightedHomogeneous generation P 4) (h : d < 4) (hp : P∈limited G d) : P=0 := by
  ext b
  rw [coeff_zero]
  by_contra hv
  have hz := (MvPolynomial.mem_restrictSupport_iff ℂ).mp hp (mem_support_iff.mpr hv)
  change height b ≤ d at hz; have he : height b = 4 := H hv
  omega

include hG in
lemma just_one (h : d < 4) (P : Label G d) : ∃ t : ℂ, P = t • Labels.unit G d := by
  obtain ⟨c,f,hf⟩ := span_four hG (raiseLabel G h.le P)
  let Q : Pol G := ∑ i : Place 0, ∑ k : Place 0, f i k • tape i k
  have he : P.val = c • (1:Pol G) + Q := by
    have hh := congr_arg (fun x : Label G 4 => x.val) hf
    change P.val = _ at hh
    simpa only [Submodule.coe_add,SetLike.val_smul, AddSubmonoidClass.coe_finsetSum,bond,Q,Labels.unit] using hh
  have hl : Q=0 := by
    refine not_thin ?_ h ?_
    · apply IsWeightedHomogeneous.sum; intro i _; apply IsWeightedHomogeneous.sum; intro k _
      rw [← MvPolynomial.C_mul']; exact (graded_tape i k).C_mul _
    rw [show Q=P.val-c • (1:Pol G) by rw [he]; abel]
    exact (limited G d).sub_mem P.property.1 ((limited G d).smul_mem c (Labels.unit G d).property.1)
  rw [hl,add_zero] at he
  exact ⟨c,Subtype.ext he⟩

include hG in
lemma below (h : d < 4) (P : (freeTable F).Field d) : ∃ t : ℂ, P=t • (freeTable F).unit d := by
  obtain ⟨P,rfl⟩ := covers F P; obtain ⟨t,rfl⟩ := just_one hG h P
  exact ⟨t,by rw [map_smul,pin_unit]⟩

include hG in
theorem dim_before (h : d < 4) : Module.finrank ℂ ((freeTable F).Field d)=1 := by
  apply (finrank_eq_one_iff_of_nonzero' ((freeTable F).unit d) ((freeTable F).alive d (table_regular F))).mpr
  intro x; obtain ⟨t,rfl⟩ := below F hG h x; exact ⟨t,rfl⟩

def keyNo (p : Plane) : ℕ := p.val.1.val*4+p.val.2.val
set_option maxRecDepth 40000 in
lemma numbering : ∀ (p q : Plane), keyNo p = keyNo q → p=q := by decide
abbrev Face := {p : Plane × Plane // keyNo p.1 ≤ keyNo p.2}

-- Fintype.card_decide via finset not reduces card? try
set_option maxRecDepth 20000 in
lemma howMany : Fintype.card (Option Face) = 22 := by decide

def sectors : Option Face → Label G 4
  | none => Labels.unit G 4
  | some p => two G 4 le_rfl p.val.1 p.val.2

include hG in
lemma up_to : ⊤ ≤ span ℂ (range (sectors (G:=G))) := by
  rw [← spanFour hG]; apply span_mono; rintro _ (rfl|⟨i,k,rfl⟩)
  exact ⟨none,rfl⟩
  rcases le_total (keyNo i) (keyNo k) with h|h
  exact ⟨some ⟨(i,k),h⟩,rfl⟩
  exact ⟨some ⟨(k,i),h⟩,two_flip _ k i⟩

def modulator (p : Face) := if p.val.1=p.val.2 then (2:ℂ)⁻¹ else 1
def portLine : Option Face → ((freeTable F).Field 4 →ₗ[ℂ] ℂ)
  | none => expectation (freeTable F) 4
  | some p => modulator p • reader F 0 p.val.1 p.val.2

include hG in
lemma separates (p q : Option Face) : portLine F p (embed F 4 (sectors q)) = if p=q then 1 else 0 := by
  classical
  rcases p with _|⟨⟨i,k⟩,hi⟩ <;> rcases q with _|⟨⟨j,g⟩,hj⟩
  · simp only [portLine,sectors,pin_unit,mean_unit (table_regular F),if_true]
  · rw [show (if (none: Option Face) = some ⟨(j,g),hj⟩ then (1:ℂ) else 0)=0 from if_neg (by simp)]; exact mean_bond ..
  · simp only [portLine, LinearMap.smul_apply,sectors,reader,negative_unit F,smul_zero]
    exact (if_neg (by simp)).symm
  simp only [portLine,sectors,LinearMap.smul_apply, reader_two F hG,modulator,Option.some.injEq,Subtype.mk.injEq,Prod.mk.injEq]
  change ((if i=k then (2:ℂ)⁻¹ else 1) • _) = if i=j ∧ k=g then 1 else 0
  have he : j=k → g=i → i=k := fun h w => numbering _ _ (Nat.le_antisymm hi (by
    change keyNo j ≤ _ at hj; rwa [h, w] at hj))
  split_ifs <;> norm_num at * <;> grind

include hG in
lemma freelance : LinearIndependent ℂ (embed F 4 ∘ sectors) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro g he i
  have hh := congr_arg (portLine F i) he
  simpa only [map_zero,map_sum,map_smul,Function.comp_apply,separates F hG,smul_eq_mul,mul_ite,
    mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true] using hh

include hG in
def stand : Module.Basis (Option Face) ℂ ((freeTable F).Field 4) := Module.Basis.mk (freelance F hG) (by
  let s := span ℂ (Set.range (sectors (G:=G)))
  have he : s.map (embed F 4) = span ℂ (range (embed F 4 ∘ sectors)) := by unfold s; rw [map_span, ← range_comp]
  rw [show s = ⊤ from eq_top_iff.mpr (up_to hG),Submodule.map_top, LinearMap.range_eq_top.mpr (covers F)] at he
  exact le_of_eq he)

include hG in
theorem four_size : Module.finrank ℂ ((freeTable F).Field 4) = 22 := by
  rw [Module.finrank_eq_card_basis (stand F hG),howMany]

end YM.UVNext.FreeStress
