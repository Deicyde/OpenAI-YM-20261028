import YM.Extra.WEAK_SCALING_ACTLAW.Color

/-!
# Weight ≤4 polynomial labels: reduction to real-order-zero curvature pairs

For use before the two-step comparator quotient. Work directly on the
constrained radial Taylor jets of the given reference polynomials. There is
no assertion here about a general invariant algebra ideal being freely
presented.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling.Color
open Function Set Tensor Labels
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge}

/-- Repaint just one chosen real color coordinate into any color. -/
def dye (A : Jet G) (i : G.ColorIndex) : G.Color →ₗ[ℝ] Jet G := by
  let F (x : G.Color) := (EuclideanSpace.proj (𝕜:=ℝ) i).smulRight x
  let B (x : G.Color) (j a) := (F x).compContinuousMultilinearMap ((A j).val a)
  have hb x j : B x j ∈ radial G j := by
    refine ⟨fun a v s => congrArg (F x) ((A j).property.1 a v s),fun z => ?_⟩
    change ∑ a, z a • F x ((A j).value a z) = 0
    simp_rw [← map_smul, ← _root_.map_sum, (A j).radial_value, map_zero]
  refine ⟨⟨(fun x j => ⟨_,hb x j⟩),fun x y => ?_⟩,fun c x => ?_⟩ <;>
    · funext j; apply Subtype.ext; funext a; ext1 u
      first | exact smul_add (((A j).val a) u i) x y | exact smul_comm (((A j).val a) u i) c x


lemma dye_colored (A : Jet G) (i : G.ColorIndex) (u : G.El) (x : G.Color) : dye A i (G.adjoint u x) = colored u (dye A i x) := by
  funext j; apply Taylor.value_ext; funext a z
  exact (map_smul (G.adjoint u) _ _).symm
lemma dyed (A : Jet G) : ∑ i, dye A i (EuclideanSpace.single i 1) = A := by
  funext j; rw [Finset.sum_apply]; apply Taylor.value_ext; funext a z; ext1 i
  simp [Taylor.value,Tensor.diagonal,dye, Pi.single_apply]
lemma jet_invariant (h : G.Simple) (f : Jet G →ₗ[ℝ] ℂ) (he : ∀ u A, f (colored u A)=f A) (A : Jet G) : f A=0 := by
  have ht i := linear_invariant h (f.comp (dye A i)) (fun g y => by simp only [LinearMap.comp_apply,dye_colored,he])
  nth_rw 1 [← dyed A]; rw [_root_.map_sum]; exact Finset.sum_eq_zero fun i _ => ht i _

private theorem layout (b : Key G →₀ ℕ) (h : height b ≤ 4) :
    b=0 ∨ (∃ k, b=Finsupp.single k 1) ∨ ∃ k j, k.1=0 ∧ j.1=0 ∧ b=Finsupp.single k 1 + Finsupp.single j 1 := by
  classical
  induction b using Finsupp.induction with
  | zero => exact Or.inl rfl
  | single_add k n b _ hn ih =>
    unfold height at h
    rw [map_add,Finsupp.weight_single, smul_eq_mul] at h
    obtain rfl|⟨j,hj⟩|⟨j,l,hj,hl,hb⟩ := ih (by unfold height; omega)
    · simp only [map_zero,add_zero,generation] at h
      have hw := k.1.zero_le
      rcases Nat.eq_or_lt_of_le (show 1 ≤ n by omega) with e|e
      · exact Or.inr (Or.inl ⟨k,by simp [← e]⟩)
      have he : n=2 := by nlinarith only [e,h,hw]
      subst n
      exact Or.inr (Or.inr ⟨k,k,by omega,by omega,by rw [add_zero,Finsupp.single_add k 1 1]⟩)
    · subst b
      rw [Finsupp.weight_single,one_smul] at h; unfold generation at h
      have hw : 0 ≤ k.1 := Nat.zero_le _
      have he : n=1 := by nlinarith only [Nat.one_le_iff_ne_zero.mpr hn,h,hw,j.1.zero_le]
      subst n
      exact Or.inr (Or.inr ⟨k,j,by omega,by omega,rfl⟩)
    · subst b; rw [map_add,Finsupp.weight_single,Finsupp.weight_single,one_smul,one_smul] at h; unfold generation at h
      rw [hj,hl] at h; have := Nat.mul_pos (Nat.pos_of_ne_zero hn) (by omega : 0 < k.1 + 2); omega

abbrev Quad (G : Gauge) := Taylor G 0 →ₗ[ℝ] Taylor G 0 →ₗ[ℝ] ℂ
private def Split (p : Pol G) := ∃ (z : ℂ) (f : Jet G →ₗ[ℝ] ℂ) (Q : Quad G),
    ∀ A : Jet G, Labels.read A p = z + f A + Q (A 0) (A 0)
private def coordL (k : Key G) := Complex.ofRealCLM.toLinearMap.comp ((axes G k.1).coord k.2)
private lemma mon_split (b : Key G →₀ ℕ) (h : height b ≤ 4) : Split (MvPolynomial.monomial b (1:ℂ)) := by
  rcases layout b h with e|⟨k,hk⟩|⟨⟨i,k⟩,⟨j,l⟩,hi,hj,rfl⟩
  · subst b; exact ⟨1,0,0,by simp⟩
  · subst b
    exact ⟨0,(coordL k).comp (LinearMap.proj (φ:=Taylor G) k.1),0,fun A => by
      rw [← MvPolynomial.X_pow_eq_monomial,pow_one]; simp [Labels.read,coordL,Labels.coord]⟩
  dsimp only at hi hj; subst i; subst j
  exact ⟨0,0,(((LinearMap.mul ℝ ℂ).comp (coordL ⟨0,k⟩)).compl₂ (coordL ⟨0,l⟩)),fun A => by
    rw [MvPolynomial.monomial_add_single,← MvPolynomial.X_pow_eq_monomial]
    simp [Labels.read,coordL,Labels.coord]⟩

private lemma separated (p : Label G 4) : Split p.val := by
  have ht := (show p.val∈limited G 4 from p.property.1)
  rw [limited,MvPolynomial.restrictSupport_eq_span] at ht
  refine Submodule.span_induction (p:=fun x _ => Split x) ?_ ⟨0,0,0,by simp⟩ ?_ ?_ ht
  · rintro _ ⟨b,hb,rfl⟩; exact mon_split b hb
  · rintro p q _ _ ⟨z,f,B,hB⟩ ⟨w,g,F,hF⟩
    exact ⟨z+w,f+g,B+F,fun A => by simp [map_add,hB,hF]; abel⟩
  · rintro c p _ ⟨z,f,B,hB⟩; exact ⟨c • z,c • f,c • B,by simp [hB, mul_add]⟩

lemma quadratic (h : G.Simple) (p : Label G 4) : ∃ (z : ℂ) (Q : Quad G), (∀ A, Labels.read A p.val=z+Q (A 0) (A 0)) ∧
    ∀ u : G.El, ∀ x y, Q (Taylor.paint u x) (Taylor.paint u y) = Q x y := by
  obtain ⟨z,f,B,hB⟩ := separated p
  have he u (x : Jet G) := p.property.2 x u
  have hp u (x : Jet G) : f (colored u x) = f x := by
    have ht := he u x; have ht' := he u (-x)
    rw [show colored u (-x) = - colored u x from funext fun _ => map_neg ..,hB,hB,map_neg] at ht'
    rw [hB,hB] at ht
    simp only [Pi.neg_apply,map_neg,LinearMap.neg_apply, neg_neg] at ht'
    apply smul_right_injective ℂ (two_ne_zero (α:=ℂ))
    change (2:ℂ) • _ = (2:ℂ) • _; simp only [two_smul]
    linear_combination ht - ht'
  have hd := jet_invariant h f hp
  have ht (u : G.El) (x : Taylor G 0) : B (Taylor.paint u x) (Taylor.paint u x)=B x x := by
    let A : Jet G := Function.update 0 0 x
    have ht := he u A; simpa [hB,hd,colored,A] using ht
  let Q : Quad G := (2:ℂ)⁻¹ • (B+B.flip)
  refine ⟨z,Q,fun A => ?_, fun u x y => ?_⟩
  · rw [hB,hd]; simp [Q,← two_smul ℂ]
  have hw := ht u (x+y); simp only [map_add,LinearMap.add_apply] at hw
  rw [ht,ht] at hw
  simp only [Q,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.flip_apply]
  congr 1
  linear_combination hw

/-! At cap five also mixed pairs. No need a particular presentation by
invariant generators even on taking the equation quotient. -/
private theorem extra (b : Key G →₀ ℕ) (h : height b ≤ 5) : height b ≤ 4 ∨ (∃ k, b=Finsupp.single k 1) ∨
    ∃ k j, k.1+j.1=1 ∧ b=Finsupp.single k 1 + Finsupp.single j 1 := by
  classical
  induction b using Finsupp.induction with
  | zero => simp [height]
  | single_add k n b _ hn ih =>
    unfold height at h
    rw [map_add,Finsupp.weight_single, smul_eq_mul] at h
    have hB : height b ≤ 4 := by
      have hp := Nat.mul_le_mul_right (generation k) (show 1 ≤ n by omega)
      unfold generation at hp h; unfold height generation; omega
    rcases layout b hB with h0|⟨j,hj⟩|⟨i,j,hi,hj,hb⟩
    · subst b
      simp [generation] at h
      rcases Nat.eq_or_lt_of_le (show 1 ≤ n by omega) with e|e
      · exact Or.inr (Or.inl ⟨k, by simp [e.symm]⟩)
      have he : n=2 := by nlinarith only [e,h,k.1.zero_le]
      subst n; left; simp [height,Finsupp.weight_single,generation]; omega
    · subst b
      rw [Finsupp.weight_single,one_smul] at h; unfold generation at h
      have h1 : n=1 := by nlinarith only [Nat.one_le_iff_ne_zero.mpr hn,h,k.1.zero_le,j.1.zero_le]
      subst n
      rcases show k.1+j.1 ≤ 1 by omega |>.eq_or_lt with he|he
      · exact Or.inr (Or.inr ⟨k,j,he,rfl⟩)
      left; simp [height,Finsupp.weight_single,generation]; omega
    · subst b; rw [map_add,Finsupp.weight_single,Finsupp.weight_single,one_smul,one_smul, generation,generation,generation,hi,hj] at h
      nlinarith only [Nat.one_le_iff_ne_zero.mpr hn,h,k.1.zero_le]

abbrev Mixed (G : Gauge) := Taylor G 0 →ₗ[ℝ] Taylor G 1 →ₗ[ℝ] ℂ
private def Split5 (p : Pol G) := ∃ (z : ℂ) (f : Jet G →ₗ[ℝ] ℂ) (Q : Quad G) (R : Mixed G),
    ∀ A : Jet G, Labels.read A p = z + f A + Q (A 0) (A 0) + R (A 0) (A 1)
private lemma mon_five (b : Key G →₀ ℕ) (h : height b ≤ 5) : Split5 (MvPolynomial.monomial b (1:ℂ)) := by
  rcases extra b h with h|⟨k,rfl⟩|⟨⟨i,k⟩,⟨j,l⟩,he,rfl⟩
  · obtain ⟨z,f,Q,hQ⟩ := mon_split b h
    exact ⟨z,f,Q,0,by simpa⟩
  · exact ⟨0,(coordL k).comp (LinearMap.proj (φ:=Taylor G) k.1),0,0,fun A => by
      rw [← MvPolynomial.X_pow_eq_monomial,pow_one]; simp [Labels.read,coordL,Labels.coord]⟩
  have aux (k : Fin (dim G 0)) (l : Fin (dim G 1)) : Split5 (MvPolynomial.monomial (Finsupp.single (⟨0,k⟩:Key G) 1 + Finsupp.single ⟨1,l⟩ 1) 1) := by
    exact ⟨0,0,0,(((LinearMap.mul ℝ ℂ).comp (coordL ⟨0,k⟩)).compl₂ (coordL ⟨1,l⟩)),fun A => by
      rw [MvPolynomial.monomial_add_single,← MvPolynomial.X_pow_eq_monomial]
      simp [Labels.read,coordL,Labels.coord]⟩
  change i+j=1 at he
  rcases Nat.eq_zero_or_pos i with h|h
  · subst i; obtain rfl := show j=1 by omega
    exact aux k l
  obtain rfl := show i=1 by omega
  obtain rfl := show j=0 by omega
  rw [add_comm]; exact aux l k

private lemma five_parts (p : Label G 5) : Split5 p.val := by
  have ht := (show p.val∈limited G 5 from p.property.1)
  rw [limited,MvPolynomial.restrictSupport_eq_span] at ht
  refine Submodule.span_induction (p:=fun x _ => Split5 x) ?_ ⟨0,0,0,0,by simp⟩ ?_ ?_ ht
  · rintro _ ⟨b,hb,rfl⟩; exact mon_five b hb
  · rintro p q _ _ ⟨z,f,B,R,hB⟩ ⟨w,g,F,S,hF⟩; exact ⟨z+w,f+g,B+F,R+S,fun A => by simp [map_add,hB,hF]; abel⟩
  · rintro c p _ ⟨z,f,B,R,hB⟩; exact ⟨c • z,c • f,c • B,c • R,by simp [hB, mul_add]⟩

lemma throughFive (h : G.Simple) (p : Label G 5) : ∃ (z : ℂ) (Q : Quad G) (R : Mixed G),
    (∀ A, Labels.read A p.val=z+Q (A 0) (A 0) + R (A 0) (A 1)) ∧
    ∀ u : G.El, ∀ x y, R (Taylor.paint u x) (Taylor.paint u y) = R x y := by
  obtain ⟨z,f,Q,R,hB⟩ := five_parts p
  have he u (x : Jet G) := p.property.2 x u
  have hp u (x : Jet G) : f (colored u x) = f x := by
    have ht := he u x; have ht' := he u (-x)
    rw [show colored u (-x) = - colored u x from funext fun _ => map_neg ..,hB,hB,map_neg] at ht'
    rw [hB,hB] at ht
    simp only [Pi.neg_apply,map_neg,LinearMap.neg_apply, neg_neg] at ht'
    apply smul_right_injective ℂ (two_ne_zero (α:=ℂ))
    change (2:ℂ) • _ = (2:ℂ) • _; simp only [two_smul]
    linear_combination ht - ht'
  have hd := jet_invariant h f hp
  refine ⟨z,Q,R,by simpa [hd] using hB,fun g x y => ?_⟩
  let J : Jet G := Function.update 0 0 x
  let K : Jet G := Function.update J 1 y
  have hQ := he g J; have hR := he g K; simp_all [J,colored,K]
end YM.Extra.WeakScaling.Color
