import YM.Push.CORRECTED_COLUMNS.Meet
import YM.Work.I01

/-!
# Radius restoration on K **even for touching large-support terms**

Input local absolute profiles on the same old K's and masks. Pay new-W
hit at expanded support. Uses `I01` on the sets of Q-cubes separated by
at least B² already. This is enough; memory reserve M d=size in our
currency. Numeric price rule explicit. `B` is the current size for the
cover, not the physical support radius of a single cell. . No
assertion that the inflations always fit at ordinary/stage exponents –
need a suitable *weak* set of parameters and their gates with this Y/Q.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.UnionK
open Set Function Filter MeasureTheory Lattice Corona RG Wilson Marker
open Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {A : Type} {V : Type*} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V] {G : Gauge} {n : Side} {P : Rep G n}
variable {v : V → Site n}

section
variable (C : A → Support n)

-- price of many incurring supports
lemma projects (B : ℕ) (hB : 8 ≤ B) (D : Support n) (k : Finset A) (h : ∀ i∈k, ¬Disjoint (C i) D)
    (hh : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → ∀ a ∈ C i, ∀ b ∈ C j, B^2 ≤ separation a b) (hk : 2≤k.card) :
    B*k.card ≤ 64*coverNumber B D := by
  classical
  choose! f hf hp using fun i hi => Finset.not_disjoint_iff.mp (h i hi)
  refine YM.Work.I01.answer n A f B hB k (fun i hi j hj he => hh i hi j hj he _ (hf i hi) _ (hf j hj)) hk D ?_
  rintro x hx; obtain ⟨i,hi,rfl⟩ := mem_image.mp hx; exact hp i hi

omit [Fintype A] in
lemma unionCover (M B : ℕ) (D : Support n) (k : Finset A) (h : ∀ i∈k, ¬Disjoint D (C i)) (hp : ∀ i∈k, coverNumber B (C i) ≤ M) :
    coverNumber B (D∪(k.biUnion C)) ≤ coverNumber B D+k.card*M := by
  induction k using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    obtain ⟨x,hD,hx⟩ := Finset.not_disjoint_iff.mp (h i (mem_insert_self ..))
    rw [Finset.card_insert_of_notMem hi, Finset.biUnion_insert, show D∪(C i∪s.biUnion C)=D∪s.biUnion C∪ C i by
      rw [union_comm (C i),← Finset.union_assoc]]
    apply (Corona.meets_sum (Finset.mem_union_left _ hD) hx B).trans
    refine (add_le_add (ih (fun i h' => h i (mem_insert_of_mem h')) (fun i h' => hp i (mem_insert_of_mem h'))) (hp i (mem_insert_self ..))).trans_eq ?_
    ring
end
section
omit [Fintype V] in
lemma tollBoost {T : Census V} {w u : ℝ} (hw : 0 < w) (v : T.Mode) : Poly.toll (fun _ => u) v=(u/w)^v.val.card*Poly.toll (fun _ => w) v := by
  unfold Poly.toll; simp only [Finset.prod_const]; rw [← mul_pow,div_mul_cancel₀ _ hw.ne']

end
section
variable {q : A × V → Site n} (Q : AddedHeads P q (Marks.all _) A)
variable (Y : ℕ ⊕ A → Poly (Marks.all (A×V))) {B : ℕ}
variable {c w u R a L : ℝ}

lemma cardinal (hrt : ∀ (i : A×V), q i∈ Q.support i.1) (i : ℕ) (t : Finset (A × V))
    (hp : ∀ x∈t, q x∈ oldSites P i) : t.card ≤ (touch Q i).card * Fintype.card V := by
  have hi : t ⊆ (touch Q i ×ˢ Finset.univ) := by
    intro x hx; refine mem_product.mpr ⟨(touch_test ..).2 ?_,Finset.mem_univ _⟩
    exact fun h => Finset.disjoint_left.mp h (hp _ hx) (hrt _)
  exact (Finset.card_le_card hi).trans_eq (by rw [card_product, Finset.card_univ])

/-- Pointwise inflation of all prices, based on actual touch counts. Need
Φ (support exponents) and packing inequalities, no selection of just one
path or one marked root. Allows extra exponential cost `L` on *first*
contact, but for more contacts uses old cover reserve. -/
theorem remap (hw : 0 < w) (hu : w ≤ u) (ha : 0 ≤ a) (q₀ : ℕ) (i : ℕ) (hL : 0≤L)
    (hG : 8≤ B)
    (hp : ∀ i j : A,i≠j → ∀ x∈ Q.support i,∀ y∈Q.support j, B^2≤ separation x y)
    (hq : ∀ j, coverNumber B (Q.support j)≤q₀) (hk : ∀ j, 1+Poly.price (fun _=>u) (Y (Sum.inr j)) ≤ Real.exp R)
    (hr : ∀ (v : A × V), q v∈Q.support v.1)
    (he : ∀ (s : Finset (A×V)), Marks.part (Y (Sum.inl i)) s≠0 → ∀ v∈s, q v∈oldSites P i)
    (hv : Real.log (u/w)*Fintype.card V+(a+1)*q₀+R ≤ L) (hc : 64*L≤B) :
    faceBill Y (fun _ => u) Q i * Real.exp ((a+1) * coverNumber B (inflate Q i)) ≤
      Real.exp L * (Poly.price (fun _ => w) (Y (Sum.inl i))*Real.exp ((a+2)*coverNumber B (oldSites P i))) := by
  let p := touch Q i
  let n := p.card
  let D := coverNumber B (oldSites P i)
  let c := Fintype.card V
  let Y' := Y (Sum.inl i)
  let X := Poly.price (fun _ => w) Y'
  have hW : 1 ≤ u/w := (one_le_div hw).2 hu
  have hU : Poly.price (fun _=>u) Y' ≤ X * Real.exp (n*(Real.log (u/w)*c)) := by
    rw [show Real.exp (n*(Real.log (u/w)*c))=(u/w)^(n*c) by
      rw [Real.exp_nat_mul,mul_comm,Real.exp_nat_mul,Real.exp_log (zero_lt_one.trans_le hW),Nat.mul_comm n,pow_mul]]
    unfold X Poly.price; rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro j _
    by_cases hj : Y'.part j=0
    · simp only [hj,norm_zero,mul_zero,zero_mul]; rfl
    have hh : j.val.card≤ n*c := cardinal Q hr _ _ (he _ hj)
    rw [mul_comm _ ((u/w)^_),← mul_assoc, tollBoost hw]
    gcongr; exact (Poly.worth (fun _ => hw) _).le
  have ht : (∏ j∈touch Q i, (1+Poly.price (fun _=>u) (Y (Sum.inr j)))) ≤ Real.exp (n*R) := by
    rw [Real.exp_nat_mul]
    exact (prod_le_prod (fun j _ => add_nonneg zero_le_one (Poly.nonnegative (fun _=>hw.trans_le hu) _))
      (fun j _ => hk j)).trans (by rw [Finset.prod_const])
  have hx : 0 ≤ Poly.price (fun _=>u) Y' := Poly.nonnegative (fun _ => hw.trans_le hu) _
  have hh := (mul_le_mul hU ht (prod_nonneg (s:=p) (fun j _ => show 0 ≤ 1+Poly.price (fun _=>u) _ from
    add_nonneg zero_le_one (Poly.nonnegative (fun _ => hw.trans_le hu) (Y (Sum.inr j))))) (hx.trans hU))
  have hN : coverNumber B (inflate Q i)≤D+n*q₀ := unionCover Q.support _ _ _ _ (fun j w => (touch_test ..).mp w) (fun j _ => hq j)
  have hz : (n:ℝ)*L ≤ L+D := by
    rcases lt_or_ge n 2 with h|h
    · have hj : (n:ℝ) ≤ 1 := by exact_mod_cast (by omega : n ≤ 1)
      exact (mul_le_mul_of_nonneg_right hj hL).trans (by rw [one_mul]; linarith [(Nat.cast_nonneg D : 0 ≤ (D:ℝ))])
    have hg : (B:ℕ)*n ≤ 64*D := projects Q.support B hG _ p (fun j hj => fun e =>
      (touch_test ..).mp hj e.symm) (fun j _ k _ E => hp j k E) h
    have hm : (B:ℝ)*n ≤ 64*D := by exact_mod_cast hg
    linarith only [hm, mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg n),hL]
  apply (mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le).trans
  refine (mul_le_mul_of_nonneg_left
    (Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast hN : (coverNumber B (inflate Q i):ℝ) ≤ (D:ℝ)+(n:ℝ)*q₀) (show 0≤a+1 by positivity)))
    (by have hw : 0 ≤ X := Poly.nonnegative (fun _ => hw) _; positivity)).trans ?_
  rw [mul_assoc X,← Real.exp_add, mul_assoc X,← Real.exp_add]
  change X*_≤Real.exp L*(X*Real.exp ((a+2)*D))
  rw [mul_left_comm (Real.exp L) X,← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (Poly.nonnegative (fun _=>hw) _)
  unfold c
  linarith only [hz,mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg n)]

/-- Collect `inflate`-hits from old-site hits. -/
theorem swollen {f g : ℕ → ℝ} (M : ℕ) {W : ℝ} (hf : ∀ i,0≤f i)
    (hw : 0 ≤ W) (hx : 0≤ u)
    (hC : ∀ i, (Q.support i).card≤M) (he : ∀ i, f i * Real.exp ((a+1)*coverNumber B (inflate Q i)) ≤ W * (g i * Real.exp ((a+2)*coverNumber B (oldSites P i))))
    (h : Ac.Hit (oldSites P) B g (a+2) u) : Ac.Hit (inflate Q) B f (a+1) ((1+(M:ℝ))*W*u) := by
  intro x
  classical
  let X := inflate Q
  let F i := if x∈ X i then f i * Real.exp ((a+1)*coverNumber B (X i)) else 0
  let G y i := if y ∈ oldSites P i then g i*Real.exp ((a+2)*coverNumber B (oldSites P i)) else 0
  let Y := Finset.univ.filter (fun i => x∈ Q.support i)
  let K := insert x (Y.biUnion Q.support)
  have ht : K.card ≤ 1+M := by
    have hY : Y.card ≤ 1 := Finset.card_le_one.mpr (fun i hi j hj => by_contra fun H =>
      Finset.disjoint_left.mp (Q.distinct i j H) (mem_filter.mp hi).2 (mem_filter.mp hj).2)
    have he : (Y.biUnion Q.support).card ≤ M := calc
      _ ≤ ∑ i∈Y, (Q.support i).card := card_biUnion_le
      _ ≤ ∑ _i∈Y, M := sum_le_sum (fun i _=>hC i)
      _ ≤ M := by simp; exact mul_le_of_le_one_left (Nat.zero_le M) hY
    exact (Finset.card_insert_le x _).trans (by omega)
  have hh y : Summable (G y) := (h y).2.1
  let p i := ∑ y∈K, W*G y i
  have hi : Summable p := summable_sum (s:=K) (f:=fun i j => W*G i j) (fun i _ => (hh i).mul_left W)
  have hF i : 0 ≤ F i := by unfold F; split; exact mul_nonneg (hf _) (Real.exp_pos _).le; rfl
  have hu i : F i≤p i := by
    unfold F; split_ifs with H
    · suffices hv : ∃ y∈K,y∈oldSites P i by
        obtain ⟨y,h1,h2⟩ := hv; apply (he i).trans
        have ht := Finset.single_le_sum (s:=K) (a:=y) (fun k _ => mul_nonneg hw (show 0≤G k i from (h k).1 i)) h1
        change W*G y i≤p i at ht; unfold G at ht; rw [if_pos h2] at ht; exact ht
      change x∈inflate Q i at H
      rcases Finset.mem_union.mp H with H|H
      · exact ⟨x,mem_insert_self ..,H⟩
      obtain ⟨j,hj,hx⟩ := mem_biUnion.mp H
      obtain ⟨y,h₁,h₂⟩ := not_disjoint_iff.mp ((touch_test ..).1 hj)
      exact ⟨y,mem_insert_of_mem (mem_biUnion.mpr ⟨j,mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,h₂⟩),h₁⟩
    exact sum_nonneg (s:=K) (fun j _ => mul_nonneg hw ((h j).1 _))
  have hz := hi.of_nonneg_of_le hF hu
  refine ⟨hF,hz,(hz.tsum_le_tsum hu hi).trans ?_⟩
  rw [show ∑' i,p i=∑ y∈K,W * ∑' i,G y i by
    simp_rw [← Summable.tsum_mul_left _ (hh _)]
    exact Summable.tsum_finsetSum fun i _ => (hh i).mul_left W]
  calc
    ∑ y∈K,W * ∑' i,G y i ≤ ∑ y∈K,W*u := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ((h i).2.2) hw
    _ ≤ _ := by
      simp only [Finset.sum_const,nsmul_eq_mul]; rw [mul_assoc (1+(M:ℝ))]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast ht) (mul_nonneg hw hx)
end
end YM.Push.Corrected.UnionK
