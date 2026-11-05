import YM.Push.ABSOLUTE_SUMS.Footprint

/-!
# Winding path support and multiplicity charges

No replacing true length by a torus number. Anchor budgets pay TRUE LENGTH and include the actual address sums. This makes it possible to pay both complete output-support exponents
(with surrounding test halos) and a true length tail. Works for every
period. Can apply to input `PathData.Bounds` on the prescribed arrays.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Paths
open RG Wilson Lattice Corona Finset Footprint
open scoped Classical Topology BigOperators
variable {n c f : Side}

section Geometry

def native (x : Site n) (w : Walk) : Support n := (visits x w).toFinset

-- also use on cover
private lemma start {V : Type*} [AddCommGroup V] [One V] (x : Four V) (w : Walk) : x ∈ visits x w := by
  cases w <;> simp [visits]
private lemma ending (x : Site n) (w : Walk) : stop x w ∈ native x w := by
  unfold native; rw [List.mem_toFinset]; induction w generalizing x with
  | nil => simp [stop,visits]
  | cons a w IH => exact List.mem_cons_of_mem x (IH (x+a.vec))
private lemma visits_cat {V : Type*} [AddCommGroup V] [One V] (x y : Four V) (w v : Walk) :
    y ∈ visits x (w++v) ↔ y ∈ visits x w ∨ y ∈ visits (stop x w) v := by
  induction w generalizing x with
  | nil =>
    simp only [List.nil_append,visits,List.mem_singleton,stop]
    exact ⟨fun h => Or.inr h, fun h => h.elim (fun hh => hh.symm ▸ start x v) id⟩
  | cons a w IH => simp only [List.cons_append,visits,List.mem_cons, IH, stop]; rw [or_assoc]
private lemma native_cat (x : Site n) (w v : Walk) :
    native x (w++v) = native x w ∪ native (stop x w) v := by
  ext; simp [native, visits_cat]

lemma to_ball (x : Site n) (w : Walk) {y : Site n} (hy : y∈native x w) : separation x y ≤ w.length := by
  unfold native at hy; rw [List.mem_toFinset] at hy
  induction w generalizing x with
  | nil => simp only [visits,List.mem_singleton] at hy; simp [hy]
  | cons a w IH =>
    rcases List.mem_cons.mp hy with rfl|h
    · simp
    have he : separation x (x+a.vec) ≤ 1 := by
      rw [separation_comm,separation,add_comm x,add_sub_cancel_right, Step.vec]; split
      · rw [pdist_neg]; exact pdist_step _
      exact pdist_step _
    have hh := IH _ h
    exact (separation_triangle x (x+a.vec) y).trans (by simp only [List.length_cons]; omega)

private lemma covered (M : ℕ) (x : Site n) (w : Walk) (h : w.length ≤ M) :
    coverNumber M (native x w) ≤ 1 := by
  have hx (y : Site n) (hy : y∈native x w) := (to_ball _ _ hy).trans h
  have he : covers M (native x w) {x} := ⟨fun y hy => halo_spec.mpr ⟨x,mem_singleton_self x,hx y hy⟩,
    ship_halo _ (by intro i hi j hj; rw [mem_singleton.mp hi,mem_singleton.mp hj])⟩
  simpa using list_cost _ he

/-- Include revisits and endpoints; chunk path into M-step pieces. -/
lemma native_cover (x : Site n) {M : ℕ} (hm : 0 < M) (w : Walk) :
    M * coverNumber M (native x w) ≤ M+w.length := by
  suffices he : ∀ k : ℕ, ∀ (x : Site n) (w : Walk), w.length=k →
      M*coverNumber M (native x w) ≤ M+k from he w.length x w rfl
  intro k; induction k using Nat.strong_induction_on with
  | h k IH =>
    intro x w hk
    by_cases h : k≤M
    · simpa only [mul_one] using le_trans (Nat.mul_le_mul_left M (covered M x w (hk ▸ h))) (by omega)
    let u := w.take M; let v := w.drop M
    have hu : u.length=M := by unfold u; rw [List.length_take,hk,min_eq_left (by omega)]
    have hv : v.length=k-M := by unfold v; rw [List.length_drop,hk]
    let y := stop x u
    have he : native x w = native x u ∪ native y v := by
      rw [← native_cat,List.take_append_drop]
    rw [he]
    have hi := meets_sum (ending x u) (show y ∈ native y v from List.mem_toFinset.mpr (start ..)) M
    apply (Nat.mul_le_mul_left M hi).trans; rw [Nat.mul_add]
    have ht := Nat.mul_le_mul_left M (covered M x u hu.le)
    rw [Nat.mul_one] at ht
    have hz := IH (k-M) (by omega) y v hv
    omega

-- Bundle of curvature slots at one anchor, length old cost as in `Atom.length`
private def slot (x : Site n) (a : Slot) := a.stencil.image (fun u => wrap n u+x)
private def walk (a : Slot) := a.walk ++ square a.plaq.val.1 a.plaq.val.2

private lemma priced (x : Site n) (a : Slot) : slot x a = native x (walk a) := by
  have he (w : Walk) (y : Cover) : (visits y w).map (fun v => wrap n v + x) = visits (wrap n y + x) w := by
    induction w generalizing y with
    | nil => simp [visits]
    | cons a w IH => simp [visits, IH, wrap_vec, add_right_comm]
  have hx : (visits (0:Cover) (walk a)).toFinset = a.stencil := by
    ext; simp [Slot.stencil, Slot.offset,walk, visits_cat]
  unfold slot native; rw [← hx]
  have hw : (visits (0:Cover) (walk a)).map (fun v => wrap n v+x) = visits x (walk a) := by
    simpa using he (walk a) 0
  rw [← hw]; ext; simp

private lemma slot_span (x : Site n) (a : Slot) (y : Site n) (h : y ∈ slot x a) : separation x y ≤ a.length := by
  rw [priced x a] at h; exact (to_ball x _ h).trans_eq (List.length_append ..)
private lemma slot_size (x : Site n) (a : Slot) (M : ℕ) (hM : 0 < M) :
    M*coverNumber M (slot x a) ≤ M+a.length := by
  rw [priced]; apply (native_cover x hM (walk a)).trans_eq
  unfold walk; rw [List.length_append]; rfl
private lemma first (x : Site n) (a : Slot) : x∈slot x a := by rw [priced]; exact List.mem_toFinset.mpr (start ..)

variable {d : ℕ}

def bundle (x : Site n) (A : Fin d → Slot) := insert x (univ.biUnion fun i => slot x (A i))
def length (A : Fin d → Slot) := ∑ i, (A i).length

lemma size (x : Site n) (A : Fin d → Slot) {M : ℕ} (hM : 0 < M) :
    M*coverNumber M (bundle x A) ≤ (1+d)*M+length A := by
  let Z (s : Finset (Fin d)) := insert x (s.biUnion fun i => slot x (A i))
  have he (s : Finset (Fin d)) : M*coverNumber M (Z s) ≤ (1+s.card)*M+∑ i∈s,(A i).length := by
    induction s using Finset.induction_on with
    | empty =>
      have he' := covered M x ([]:Walk) (by simp)
      simpa [Z,native,visits] using (show M*coverNumber M (native x []) ≤ M*1 from
        Nat.mul_le_mul_left M he')
    | @insert a s ha IH =>
      have eq : Z (insert a s) = slot x (A a) ∪ Z s := by ext i; simp [Z]
      rw [eq,sum_insert ha,card_insert_of_notMem ha]
      apply (Nat.mul_le_mul_left M (meets_sum (first x (A a)) (show x∈Z s from mem_insert_self ..) M)).trans
      have hi := slot_size x (A a) M hM
      nlinarith
  simpa only [card_univ,Fintype.card_fin,Z,bundle,length] using he univ

lemma where_slot (x : Site n) (A : Fin d → Slot) (y : Site n) (h : y∈bundle x A) :
    separation x y ≤ length A := by
  rcases mem_insert.mp h with rfl|h
  · simp
  obtain ⟨i,hi,h⟩ := mem_biUnion.mp h
  exact (slot_span x (A i) y h).trans (Finset.single_le_sum (f:=fun i => (A i).length) (fun j _ =>
    Nat.zero_le _) hi)
end Geometry

section Charges
variable {d : ℕ} {ι : Type*} (p : Ratio c f) (l B : ℕ)

def baseFee := preCost l + conversion p l*(1+(d:ℝ))
def legFee := conversion p l / (B:ℝ)
-- charge W uses `B`; need post-L.
def originFee := l*B+1

lemma pay_locations (o : Site f) (A : Fin d → Slot) (Y : Support c)
    (h : Y ⊆ enlargement p l B (bundle o A)) : ∀ y ∈ Y,
    separation y (p.parent o) ≤ originFee l B * (1+length A) := by
  intro y hy; obtain ⟨x,hx,he⟩ := halo_spec.mp (h hy)
  obtain ⟨x,hx',rfl⟩ := mem_image.mp hx
  have hv := where_slot o A x hx'
  have hr := foreshorten p o x
  have hm : 1 ≤ p.count.val := p.count.property
  have hi : separation (p.parent o) (p.parent x) ≤ separation o x + 1 := by
    apply Nat.le_of_mul_le_mul_left _ (show 0 < p.count.val from hm)
    calc
      _ ≤ _ := hr
      _ ≤ _ := by rw [Nat.mul_add,Nat.mul_one]
                  exact Nat.add_le_add_right (by nth_rw 1 [← one_mul (separation o x)]
                                                 exact Nat.mul_le_mul_right _ hm) _
  rw [separation_comm y]
  apply (separation_triangle (p.parent o) (p.parent x) _).trans
  unfold originFee; nlinarith

lemma pay_bundle (o : Site f) (A : Fin d → Slot) (Y : Support c)
    (h : Y ⊆ enlargement p l B (bundle o A)) (hB : 0 < B) :
    (coverNumber B Y:ℝ) ≤ baseFee (d:=d) p l + legFee p l B * length A := by
  have he := footprint p l B B (bundle o A) hB (by omega)
  apply le_trans _ (le_trans he ?_)
  · exact_mod_cast cover_mono h B
  have hp : 0 < (B:ℝ) := by exact_mod_cast hB
  have hi : (B:ℝ)*coverNumber B (bundle o A) ≤ (1+(d:ℝ))*B+length A := by
    exact_mod_cast size o A hB
  have hh : 0 ≤ conversion p l := by unfold conversion preCost; positivity
  unfold baseFee legFee; field_simp; nlinarith [mul_le_mul_of_nonneg_left hi hh]

/-- Output hit with COMPLETE path coefficients at common anchors.
The tail here is in TRUE length, with full cover charges and any fixed
polynomial true-length costs. -/
theorem bundle_hit (A : ι → Fin d → Slot) {σ Γ : ℝ} (w : ι → ℝ) (_hσ : 0 < σ)
    (hw : ∀ i, 0≤w i) (h : SumBudget (fun i => w i * Real.exp (σ*length (A i))) Γ)
    (Y : Site f × ι → Support c) (hy : ∀ i, Y i ⊆ enlargement p l B (bundle i.1 (A i.2)))
    (hB : 0 < B) {C a ε : ℝ} (hC : 0 ≤ C) (hr : reserve σ a (legFee p l B) ε)
    (k : ℕ) (g : Site f × ι → ℝ) (hg : ∀ i, 0≤g i)
    (he : ∀ i, g i ≤ C*w i.2*(1+(length (A i.2):ℝ))^k) (m : ℕ) (x : Site c) :
    SumBudget (fun i => if m ≤ length (A i.2) then (if x∈Y i then
      g i*Real.exp (a*coverNumber B (Y i)) else 0) else 0)
      (payment (p.count.val^4) (originFee l B) k ε C Γ a (baseFee (d:=d) p l) * Real.exp (-ε)^m) := by
  have hp : Footprint.Anchored (Prod.fst (α:=Site f) (β:=ι)) (w ∘ Prod.snd)
      (fun i => length (A i.2)) σ Γ := by
    let b (x : Site f) (i : Site f) := if i=x then (1:ℝ) else 0
    have hb x : SumBudget (b x) 1 := budget_finite (fun i => by unfold b; split <;> norm_num) (by simp [b])
    intro x
    convert budget_prod (hb x) h using 1
    · ext i; simp [b]
    simp
  refine assigned_tail p.parent _ (crowd p) Prod.fst (w ∘ Prod.snd) (fun i => hw i.2)
    _ Y hp (originFee l B) k B (fun i x hx => pay_locations p l B _ (A i.2) _ (hy i) x hx)
    (fun i => pay_bundle p l B _ _ _ (hy i) hB) hC hr g hg he m x
end Charges
section Applications
variable {G : Gauge} {d : ℕ} (p : Ratio c f) (l B : ℕ)

lemma atom_foot (x : Site f) (A : Atom G d) : A.footprint x = bundle x A.leg := by
  unfold Atom.footprint Atom.stencil bundle slot
  rw [image_insert]; simp only [map_zero,zero_add]; congr 1
  ext i; simp [Finset.mem_image, Finset.mem_biUnion]; tauto



/-- Ordered pairs of row labels (squares) at fixed root type. Other
root types are finite pre-L. The sum is not over pairs of positions
only. Any other cost from a kept-row test needs to be checked as well;
if it fits in the surrounding halo use l here including THAT expense. -/
def duplex (R : PathData G) (r : PlaqAxes) (i : ℕ × ℕ) : Fin 2 → Slot :=
  ![(R.row r i.1).2,(R.row r i.2).2]

def mate (R : PathData G) (r : PlaqAxes) (i : ℕ × ℕ) := |(R.row r i.1).1| * |(R.row r i.2).1|

lemma duplex_price (R : PathData G) (r : PlaqAxes) (i : ℕ × ℕ) : length (duplex R r i) =
    (R.row r i.1).2.length + (R.row r i.2).2.length := by simp [length,duplex,Fin.sum_univ_succ]


end Applications
end YM.Push.AbsoluteSums.Paths
