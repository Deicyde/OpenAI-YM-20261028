import YM.UVNext.FREE_STRESS_CERTIFICATE.Couplings

/-!
# Classification of actual gauge-invariant labels through weight five

No equation ideal or detector antecedent. Use on all choices of `Frames`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Labels MvPolynomial Function
variable {G : Gauge} {j l d : ℕ}

private abbrev oneKey (i : Key G) : Key G →₀ ℕ := Finsupp.single i 1
private lemma peel (u : Key G →₀ ℕ) (hu : u ≠ 0) :
    ∃ i : Key G, ∃ v : Key G →₀ ℕ, u=v+oneKey i := by
  obtain ⟨i,hi⟩ : u.support.Nonempty := by simpa using hu
  exact ⟨i,u-oneKey i,(tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr
    (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)))).symm⟩

private lemma height_step (u : Key G →₀ ℕ) (i : Key G) : height (u+oneKey i) = height u + i.1 + 2 := by
  rw [height,map_add,Finsupp.weight_single,one_smul,generation,← add_assoc,height]

private lemma heavy (u : Key G →₀ ℕ) (hu : u ≠ 0) : 2 ≤ height u := by
  obtain ⟨i,v,rfl⟩ := peel u hu; rw [height_step]; omega

private lemma tiny {u : Key G →₀ ℕ} (h : height u ≤ 5) : u = 0 ∨ (∃ i, u=oneKey i) ∨
    ∃ i k : Key G, u=oneKey i+oneKey k ∧ i.1 = 0 ∧ k.1 ≤ 1 := by
  by_cases he : u=0
  · exact Or.inl he
  right
  obtain ⟨i,v,rfl⟩ := peel _ he
  rw [height_step] at h
  by_cases hv : v=0
  · subst v; exact Or.inl ⟨i,zero_add _⟩
  right
  obtain ⟨k,w,rfl⟩ := peel v hv
  rw [height_step] at h
  have he : w=0 := by by_contra ht; have := heavy w ht; omega
  subst w; rw [zero_add]
  by_cases ht : k.1 = 0
  · exact ⟨k,i,rfl,ht,by omega⟩
  exact ⟨i,k,add_comm _ _,by omega,by omega⟩

abbrev Bi (G : Gauge) (j l : ℕ) := Taylor G j →ₗ[ℝ] Taylor G l →ₗ[ℝ] ℂ

/-- Evaluation envelope for weighted monomials; use even and odd
parts to recover the invariances of the coefficient forms. -/
private def Shelf (G : Gauge) (d : ℕ) : Submodule ℂ (Pol G) where
  carrier := {p | ∃ (c : ℂ) (e : Jet G →ₗ[ℝ] ℂ) (B : Bi G 0 0) (D : Bi G 0 1),
    (d < 5 → D=0) ∧ ∀ A, Labels.read A p = c+e A+B (A 0) (A 0)+D (A 0) (A 1)}
  zero_mem' := ⟨0,0,0,0,fun _ => rfl,by simp⟩
  add_mem' := by
    rintro p q ⟨c,e,B,D,h,H⟩ ⟨w,f,b,L,i,I⟩
    refine ⟨c+w,e+f,B+b,D+L,fun z => by rw [h z,i z,add_zero],?_⟩
    intro A; simp [H,I]; abel
  smul_mem' := by
    rintro t p ⟨c,e,B,D,h,H⟩
    exact ⟨t*c,t • e,t • B,t • D, fun z => by rw [h z,smul_zero],by
      intro A; simp [H,mul_add]⟩

private def decoder (i : Fin (Labels.dim G j)) : Taylor G j →ₗ[ℝ] ℂ :=
  Complex.ofRealLI.toLinearMap.comp ((axes G j).coord i)

private def productOf (a : Taylor G j →ₗ[ℝ] ℂ) (b : Taylor G l →ₗ[ℝ] ℂ) : Bi G j l :=
  (((LinearMap.mul ℝ ℂ).comp a).flip.comp b).flip

private theorem prepared (P : Label G d) (h : d ≤ 5) : P.val ∈ Shelf G d := by
  have he : P.val ∈ limited G d := P.property.1
  rw [limited, MvPolynomial.restrictSupport_eq_span] at he
  refine (Submodule.span_le.mpr ?_ : Submodule.span ℂ _ ≤ Shelf G d) he
  rintro _ ⟨u,hu,rfl⟩
  change height u ≤ d at hu
  rcases tiny (hu.trans h) with rfl | ⟨i,rfl⟩ | ⟨⟨j,i⟩,⟨l,k⟩,rfl,hj,hk⟩
  · refine ⟨1,0,0,0,fun _ => rfl,fun A => ?_⟩
    simp
  · obtain ⟨j,i⟩ := i
    refine ⟨0,(decoder i).comp (LinearMap.proj j),0,0,fun _ => rfl,fun A => ?_⟩
    change Labels.read A (X ⟨j,i⟩) = _
    simp [Labels.read,decoder,Labels.coord]
  · change j=0 at hj; subst j
    change l≤1 at hk
    have hQ {a b : Key G} (A : Jet G) : Labels.read A (monomial (oneKey a + oneKey b) 1) =
        decoder a.2 (A a.1) * decoder b.2 (A b.1) := by
      rw [monomial_add_single,pow_one,map_mul]
      change Labels.read A (X _) * Labels.read A (X _) = _
      simp [Labels.read, decoder,Labels.coord]
    interval_cases l
    · refine ⟨0,0,productOf (decoder i) (decoder k),0,fun _ => rfl,fun A => ?_⟩
      simpa only [LinearMap.zero_apply, add_zero, zero_add] using! hQ (a:=⟨0,i⟩) (b:=⟨0,k⟩) A
    · have hd : 5 ≤ d := by
        rw [height_step,height,Finsupp.weight_single,one_smul,generation] at hu
        exact hu
      refine ⟨0,0,0,productOf (decoder i) (decoder k),fun ht => (ht.not_ge hd).elim,fun A => ?_⟩
      simpa only [LinearMap.zero_apply, add_zero,zero_add] using! hQ (a:=⟨0,i⟩) (b:=⟨1,k⟩) A

private def paired (x : Taylor G 0) (y : Taylor G 1) : Jet G := Pi.single 0 x + Pi.single 1 y

@[simp] private theorem paired_zero (x : Taylor G 0) (y : Taylor G 1) : paired x y 0=x := by simp [paired]
@[simp] private theorem paired_one (x : Taylor G 0) (y : Taylor G 1) : paired x y 1=y := by simp [paired]

set_option maxHeartbeats 2000000 in
private lemma average_color (hG : G.Simple) (P : Label G d) (h : d ≤ 5) :
    ∃ (c : ℂ) (B : Bi G 0 0) (D : Bi G 0 1),
      (∀ u x y, B (Taylor.paint u x) (Taylor.paint u y) = B x y) ∧
      (∀ u x y, D (Taylor.paint u x) (Taylor.paint u y) = D x y) ∧ (d < 5 → D=0) ∧
      ∀ A, Labels.read A P.val = c+B (A 0) (A 0)+D (A 0) (A 1) := by
  obtain ⟨c,e,M,D,hD,H⟩ := prepared P h
  let B : Bi G 0 0 := (1/2:ℂ) • (M+M.flip)
  have Hs (x) : B x x = M x x := by dsimp [B]; ring
  have hb (x y) : B x y = B y x := by dsimp [B]; rw [add_comm]
  have he (A : Jet G) (u : G.El) := P.property.2 A u
  have hf : e=0 := by
    apply no_jet_linear hG _
    intro u A
    have h1 := he A u; have h2 := he (-A) u
    simp_rw [H] at h1 h2
    rw [show colored u (-A) = - colored u A from funext fun i => (Taylor.paint u).map_neg _] at h2
    simp only [map_neg,Pi.neg_apply,LinearMap.neg_apply,neg_neg] at h2
    linear_combination (norm:=ring1) h1/2 - h2/2
  simp only [hf,LinearMap.zero_apply, add_zero, ← Hs] at H
  have h0 (x : Taylor G 0) (y : Taylor G 1) (u : G.El) := he (paired x y) u
  simp_rw [H, colored,paired_zero,paired_one] at h0
  have h1 (x : Taylor G 0) (u : G.El) := h0 x 0 u
  simp_rw [map_zero, add_zero, add_right_inj] at h1
  refine ⟨c,B,D,fun u x y => ?_,fun u x y => add_left_cancel (by
    have h2 := h0 x y u
    rwa [h1] at h2),hD,H⟩
  have h2 := h1 (x+y) u
  simp only [map_add, LinearMap.add_apply,h1, hb y x, hb (Taylor.paint u y) (Taylor.paint u x)] at h2
  linear_combination h2/2

lemma span_four (hG : G.Simple) (P : Label G 4) :
    ∃ (c : ℂ) (f : Place 0 → Place 0 → ℂ), P = c • Labels.unit G 4 + ∑ i, ∑ k, f i k • bond i k (show 0+0+4 ≤ 4 from le_rfl) := by
  obtain ⟨w,F,T,hF,-,ht,he⟩ := average_color hG P (by decide)
  obtain ⟨a,ha⟩ := component_form hG F hF
  refine ⟨w,a,?_⟩
  apply Subtype.ext; apply Labels.eval_ext; intro A
  rw [he,ha,ht (by decide)]
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, Submodule.coe_add, bond, Labels.unit, map_add,map_sum,map_smul, map_one,
    Complex.real_smul, eval_tape, smul_eq_mul, LinearMap.zero_apply,add_zero,mul_one]
  congr 1
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => mul_comm _ _

lemma span_five (hG : G.Simple) (P : Label G 5) :
    ∃ (c : ℂ) (f : Place 0 → Place 0 → ℂ) (r : Place 0 → Place 1 → ℂ),
      P = c • Labels.unit G 5 + (∑ i, ∑ k, f i k • bond i k (show 0+0+4 ≤ 5 by decide)) +
        ∑ i, ∑ k, r i k • bond i k (show 0+1+4 ≤ 5 from le_rfl) := by
  obtain ⟨w,F,T,hF,hT,-,he⟩ := average_color hG P (by decide)
  obtain ⟨a,ha⟩ := component_form hG F hF
  obtain ⟨b,hb⟩ := component_form hG T hT
  refine ⟨w,a,b,?_⟩
  apply Subtype.ext; apply Labels.eval_ext; intro A
  rw [he,ha,hb]
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, Submodule.coe_add, bond, Labels.unit, map_add,map_sum,map_smul, map_one,
    Complex.real_smul, eval_tape, smul_eq_mul,mul_one]
  apply congr_arg₂ (·+·)
  · congr 1; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro k _; rw [mul_comm]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro k _; rw [mul_comm]

end YM.UVNext.FreeStress
