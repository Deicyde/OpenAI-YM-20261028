import YM.UVNext.FREE_STRESS_CERTIFICATE.Low

/-! Oriented-axis format for the low coefficient spaces. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Labels Submodule Function
variable {G : Gauge} {d : ℕ}

abbrev Plane := {p : Axis × Axis // p.1 < p.2}

def two (G : Gauge) (d : ℕ) (h : 4 ≤ d) (i k : Plane) : Label G d :=
  ff G d h i.val.1 i.val.2 k.val.1 k.val.2

def mixed (G : Gauge) (d : ℕ) (h : 5 ≤ d) (i k : Plane) (a : Axis) : Label G d :=
  fq G d h i.val.1 i.val.2 k.val.1 k.val.2 a

theorem ff_left (h : 4 ≤ d) (a b c e : Axis) : ff G d h b a c e = -ff G d h a b c e := bond_left (initialPlace a b) (initialPlace c e) h
theorem ff_right (h : 4 ≤ d) (a b c e : Axis) : ff G d h a b e c = -ff G d h a b c e := bond_right (initialPlace a b) (initialPlace c e) h
theorem fq_left (h : 5 ≤ d) (a b c e k : Axis) : fq G d h b a c e k = -fq G d h a b c e k := bond_left (initialPlace a b) (gradientPlace c e k) h
theorem fq_right (h : 5 ≤ d) (a b c e k : Axis) : fq G d h a b e c k = -fq G d h a b c e k := bond_right (initialPlace a b) (gradientPlace c e k) h

theorem no_negative {A : Label G d} (he : A = -A) : A=0 := by
  have ht : (2:ℂ) • A = 0 := by rw [two_smul]; nth_rw 1 [he]; simp
  exact (smul_eq_zero.mp ht).resolve_left (by norm_num)

@[simp] theorem ff_selfL (h : 4 ≤ d) (a c e : Axis) : ff G d h a a c e = 0 := no_negative (ff_left ..)
@[simp] theorem ff_selfR (h : 4 ≤ d) (a b c : Axis) : ff G d h a b c c = 0 := no_negative (ff_right ..)
@[simp] theorem fq_selfL (h : 5 ≤ d) (a c e r : Axis) : fq G d h a a c e r = 0 := no_negative (fq_left ..)
@[simp] theorem fq_selfR (h : 5 ≤ d) (a b c r : Axis) : fq G d h a b c c r = 0 := no_negative (fq_right ..)

theorem two_flip (h : 4 ≤ d) (p q : Plane) : two G d h p q = two G d h q p := ff_swap ..

theorem oriented_mem (h : 4 ≤ d) (U : Submodule ℂ (Label G d))
    (H : ∀ i k, two G d h i k ∈ U) (a b c e : Axis) : ff G d h a b c e ∈ U := by
  have he (p : Plane) (c e : Axis) : ff G d h p.val.1 p.val.2 c e ∈ U := by
    rcases lt_trichotomy c e with hx|hx|hx
    · exact H p ⟨(c,e),hx⟩
    · subst c; simp
    rw [ff_right _ _ _ e c]; exact U.neg_mem (H p ⟨(e,c),hx⟩)
  rcases lt_trichotomy a b with hx|hx|hx
  · exact he ⟨(a,b),hx⟩ c e
  · subst a; simp
  rw [ff_left _ b a]; exact U.neg_mem (he ⟨(b,a),hx⟩ c e)

theorem oriented_mixed (h : 5 ≤ d) (U : Submodule ℂ (Label G d))
    (H : ∀ i k a, mixed G d h i k a ∈ U) (a b c e r : Axis) : fq G d h a b c e r ∈ U := by
  have he (p : Plane) (c e r : Axis) : fq G d h p.val.1 p.val.2 c e r ∈ U := by
    rcases lt_trichotomy c e with hx|hx|hx
    · exact H p ⟨(c,e),hx⟩ r
    · subst c; simp
    rw [fq_right _ _ _ e c]; exact U.neg_mem (H p ⟨(e,c),hx⟩ r)
  rcases lt_trichotomy a b with hx|hx|hx
  · exact he ⟨(a,b),hx⟩ c e r
  · subst a; simp
  rw [fq_left _ b a]; exact U.neg_mem (he ⟨(b,a),hx⟩ c e r)

theorem bond_initial {h : 0+0+4 ≤ d} (p q : Place 0) : bond (G:=G) p q h = ff G d h p.1.1 p.1.2 q.1.1 q.1.2 := by
  unfold ff
  congr 1 <;> exact Prod.ext rfl (Subsingleton.elim ..)

theorem bond_gradient {h : 0+1+4 ≤ d} (p : Place 0) (q : Place 1) :
    bond (G:=G) p q h = fq G d h p.1.1 p.1.2 q.1.1 q.1.2 (q.2 0) := by
  unfold fq
  congr 1
  · exact Prod.ext rfl (Subsingleton.elim ..)
  exact Prod.ext rfl (funext fun a => congr_arg q.2 (Subsingleton.elim a 0))

abbrev fourGens (G : Gauge) := {p : Label G 4 | p=Labels.unit G 4 ∨ ∃ i k : Plane, p=two G 4 le_rfl i k}
abbrev fiveGens (G : Gauge) := {p : Label G 5 | p=Labels.unit G 5 ∨
  (∃ i k, p=two G 5 (by decide) i k) ∨ ∃ i k a, p=mixed G 5 le_rfl i k a}

theorem spanFour (hG : G.Simple) : span ℂ (fourGens G) = ⊤ := by
  refine eq_top_iff.mpr fun p _ => ?_
  let U := span ℂ (fourGens G)
  obtain ⟨c,f,h⟩ := span_four hG p
  rw [h]; refine U.add_mem (U.smul_mem c (subset_span (Or.inl rfl)))
    (sum_mem fun i _ => sum_mem fun k _ => U.smul_mem _ ?_)
  rw [bond_initial]; exact oriented_mem le_rfl U (fun i k => subset_span (Or.inr ⟨i,k,rfl⟩)) _ _ _ _

theorem spanFive (hG : G.Simple) : span ℂ (fiveGens G) = ⊤ := by
  refine eq_top_iff.mpr fun p _ => ?_
  let U := span ℂ (fiveGens G)
  obtain ⟨c,f,r,h⟩ := span_five hG p
  rw [h]; refine U.add_mem (U.add_mem (U.smul_mem c (subset_span (Or.inl rfl)))
    (sum_mem fun i _ => sum_mem fun k _ => U.smul_mem _ ?_))
    (sum_mem fun i _ => sum_mem fun k _ => U.smul_mem _ ?_)
  · rw [bond_initial]; exact oriented_mem _ U (fun i k => subset_span (Or.inr (Or.inl ⟨i,k,rfl⟩))) _ _ _ _
  rw [bond_gradient]; exact oriented_mixed _ U (fun i k a => subset_span (Or.inr (Or.inr ⟨i,k,a,rfl⟩))) _ _ _ _ _

end YM.UVNext.FreeStress
