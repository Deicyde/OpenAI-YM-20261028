import YM.Push.RELAY_DIFFERENCE.RawTop
import YM.Push.RELAY_DIFFERENCE.TwoSided

/-!
# Iterating the mixed derivatives at a healthy point

No switch to a symmetric Fréchet-derivative norm.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference.TwoSided
open Function Set Filter MeasureTheory Wilson RG Lattice Cells Bid
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {n : Side}
variable {U : Config G n} {f : Config G n → ℂ} {k d : ℕ}

/-- Differentiating across a swap already done nearer the operator. -/
theorem swap (H : Based U f k) (p q : List (Move G n)) (A B : Directions G n)
    (he : p.length+q.length+2 ≤ k) :
    mult f (p ++ l A::r B::q) U = mult f (p ++ r B::l A::q) U := by
  induction p generalizing U with
  | nil =>
    exact ((H.less (show 2+q.length ≤ k from by simpa [add_comm] using he)).series q).commutes A B
  | cons a p ih =>
    simp only [List.cons_append, mult]
    exact (show (fun t : ℝ => mult f (p++l A::r B::q) (vary U (t • a))) =ᶠ[𝓝 0]
        (fun t : ℝ => mult f (p++r B::l A::q) (vary U (t • a))) from
      (H.moves a).mono fun t ht => ih ht (by simp only [List.length_cons] at he; omega)).deriv_eq

lemma split_after (H : Based U f k) (p q : List (Move G n)) (A : Move G n)
    (he : p.length+q.length+1 ≤ k) :
    mult f (p ++ A::q) U=mult f (p ++ l A.1::q) U+mult f (p ++ r A.2::q) U := by
  induction p generalizing U with
  | nil => exact ((H.less (by simpa only [List.length_nil,zero_add,add_comm] using he)).series q).split A
  | cons a p ih =>
    simp only [List.length_cons] at he
    have hF (B : Move G n) : Based U (mult f (p ++ B :: q)) 1 :=
      (H.less (by simp; omega : 1+(p ++ B :: q).length ≤ k)).series _
    simp only [List.cons_append,mult]
    have hh : (fun t : ℝ => mult f (p++A::q) (vary U (t • a))) =ᶠ[𝓝 0]
        (fun t : ℝ => mult f (p++l A.1::q) (vary U (t • a))+mult f (p++r A.2::q) (vary U (t • a))) :=
      (H.moves a).mono fun t ht => ih ht (by omega)
    apply hh.deriv_eq.trans <|
      deriv_fun_add ((hF (l A.1)).approach a).differentiableAt ((hF (r A.2)).approach a).differentiableAt

lemma split_R (H : Based U f k) (p q : List (Move G n)) (a : List (Directions G n)) (B : Directions G n)
    (he : p.length+q.length+a.length+1 ≤ k) :
    mult f (p ++ a.map l ++ r B :: q) U = mult f (p ++ r B :: (a.map l ++ q)) U := by
  induction a generalizing p with
  | nil => simp
  | cons A a ih =>
    simp only [List.length_cons] at he
    have ht := ih (p++[l A]) (by simp; omega)
    have hs := swap H p (a.map l ++ q) A B (by simp; omega)
    simpa only [List.map_cons,List.cons_append,List.append_assoc, List.nil_append] using
      ht.trans (by simpa only [List.append_assoc,List.cons_append, List.nil_append] using hs)

lemma split_L (H : Based U f k) (p q : List (Move G n)) (a : List (Directions G n)) (A : Directions G n)
    (he : p.length+q.length+a.length+1 ≤ k) :
    mult f (p ++ l A :: (a.map r ++ q)) U = mult f (p ++ a.map r ++ l A :: q) U := by
  induction a generalizing p with
  | nil => simp
  | cons B a ih =>
    simp only [List.length_cons] at he
    have ht := ih (p++[r B]) (by simp; omega)
    have hs := swap H p (a.map r ++ q) A B (by simp; omega)
    simpa only [List.map_cons,List.cons_append,List.append_assoc, List.nil_append] using
      (show mult f (p ++ l A :: r B :: (a.map r ++ q)) U = mult f (p ++ [r B] ++ a.map r ++ l A :: q) U from
        hs.trans (by simpa only [List.append_assoc,List.cons_append, List.nil_append] using ht))

section Prices
variable (P : BudgetPoint) (x : Site n) {c M : ℝ} {Z : Support n}

def quota (M : ℝ) (A : Directions G n) := P.dirBound x (M⁻¹ • A)

lemma quota_u {A : Directions G n} (H : quota P x M A) : quota P x M (recolor U A) := by
  intro i
  change ‖M⁻¹ • G.adjoint _ _‖ ≤ _
  rw [←map_smul,G.norm_adjoint]; exact H i

lemma prepared_cost (H : Based U f P.order) (hp : P.supBounds x Z f c) (hm : Healthy P.threshold Z U)
    (hM : 1 ≤ M) (a b : List (Directions G n)) (ha : ∀ i∈a,quota P x M i) (hb : ∀ i∈b,quota P x M i)
    (he : a.length+b.length ≤ P.order) :
    ‖mult f (a.map r ++ b.map l) U‖ ≤ M^P.order*c := by
  induction a generalizing b with
  | nil =>
    simp only [List.map_nil,List.nil_append,lefts]
    have hx : 0 < M := zero_lt_one.trans_le hM
    let q := b.map fun A => M⁻¹ • A
    have hl : q.length ≤ P.order := by simpa only [q,List.length_map,List.length_nil,zero_add] using he
    have ho : q.map (fun A => M • A) = b := by simp [q,comp_def,hx.ne']
    rw [←ho,left_dilate,norm_smul_of_nonneg (pow_nonneg hx.le _)]
    exact mul_le_mul (pow_le_pow_right₀ hM hl)
      (hp.2 _ hm _ hl fun i hi => by obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hi; exact hb y hy)
      (norm_nonneg _) (pow_nonneg hx.le _)
  | cons A a ih =>
    change ‖op _ _ _‖ ≤ _
    rw [exchange]
    have hl : 0+(b.map l).length+a.length+1 ≤ P.order := by simp only [List.length_map,List.length_cons] at *;omega
    change ‖mult f (l (recolor U A) :: (a.map r ++ b.map l)) U‖ ≤ _
    have ht := split_L H [] (b.map l) a (recolor U A) hl
    simp only [List.nil_append] at ht
    rw [ht]
    have hf : quota P x M (recolor U A) := quota_u _ _ (ha A (List.mem_cons_self ..))
    apply ih (recolor U A :: b) (fun j hj => ha _ (List.mem_cons_of_mem _ hj))
    · intro i hi; rcases List.mem_cons.mp hi with h|h
      · subst i; exact hf
      exact hb i h
    simp only [List.length_cons] at *; omega

/-- Only a `2^k` cost after scaling; no spent derivative or support
price in reversing any linked directions. -/
lemma many (H : Based U f P.order) (hp : P.supBounds x Z f c) (hm : Healthy P.threshold Z U)
    (hM : 1 ≤ M) (a b : List (Directions G n)) (q : List (Move G n))
    (ha : ∀ i∈a,quota P x M i) (hb : ∀ i∈b,quota P x M i)
    (hq : ∀ i∈q,quota P x M i.1 ∧ quota P x M i.2)
    (he : a.length+b.length+q.length ≤ P.order) :
    ‖mult f (a.map r ++ b.map l ++ q) U‖ ≤ 2^q.length*(M^P.order*c) := by
  let w := M^P.order*c
  induction q generalizing a b with
  | nil => simpa using prepared_cost P x H hp hm hM a b ha hb he
  | cons A q ih =>
    simp only [List.length_cons] at he
    have hg (i) (hi : i∈q) := hq i (List.mem_cons_of_mem _ hi)
    obtain ⟨hL,hR⟩ := hq A (List.mem_cons_self ..)
    have hs := split_R H (a.map r) q b A.2 (by simp; omega)
    rw [split_after H (a.map r ++ b.map l) q A (by simp; omega), hs,List.length_cons]
    have hh : ‖mult f ((a.map r ++ b.map l) ++ l A.1 :: q) U‖ ≤ 2^q.length*w := by
      have he' := ih a (b ++ [A.1]) ha (fun i hi => by simp only [List.mem_append,List.mem_singleton] at hi; exact hi.elim (hb _) fun he => he ▸ hL) hg
        (by simp;omega)
      simpa only [List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.cons_append,List.nil_append] using he'
    have ht : ‖mult f (a.map r ++ r A.2 :: (b.map l ++ q)) U‖ ≤ 2^q.length*w := by
      have he' := ih (a ++ [A.2]) b (fun i hi => by simp only [List.mem_append,List.mem_singleton] at hi; exact hi.elim (ha _) fun he => he ▸ hR) hb hg
        (by simp;omega)
      simpa only [List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.cons_append,List.nil_append] using he'
    apply (norm_add_le ..).trans ((add_le_add hh ht).trans_eq ?_)
    unfold w; ring
end Prices
end YM.Push.RelayDifference.TwoSided
