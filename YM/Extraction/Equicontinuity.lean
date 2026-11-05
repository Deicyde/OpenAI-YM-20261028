import YM.Extraction.Center
import YM.Extraction.Difference
import YM.Extraction.Gaps

/-! The equicontinuity producer for primaries is ready to USE the finite cutoff estimates.

Proof path: Bricks, verified finite Schatten-Hadamard argument & true cyclic reimpl,
axis gap scheduling in native units, oriented room on fixed-p/expanding p separately,
deterministic hybrid telescope to use arbitrary grid tags through patch boundary.
No equicontinuity through ties. No assuming expansion global bounds from local compact
extraction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction.Difference
open Function Filter Set Lattice MeasureTheory Metric Gaps Wilson Slice.Time
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G}

abbrev positions (n : ℕ) := Fin n → Cover

/-- Moves by ONE whole component, positive. -/
def advance {n : ℕ} (s : positions n) (k : Fin n) (i : Axis) (l : ℕ) : positions n := update s k (s k + (l • step i))

lemma shifted {m N p : ℕ} (v : Fin (m+1) → C.book.Token) (a : positions (m+1)) (k : Fin (m+1)) (i : Axis) (l : ℕ) :
    lifted C N p v (advance a k i l) = C.numeric N p v (update (wrap _ ∘ a) k (wrap (C.side N p) (a k) + offset i (↑l))) := by
  unfold lifted
  congr 1; funext j; by_cases he : j=k
  · subst j; simp only [Function.comp_apply,advance,update_self,map_add,map_nsmul,wrap_step]; congr 1; ext1; simp [offset]
  simp [advance,he]

private theorem norm_tag {m : ℕ} (x y : positions m) (t : ℝ) :
    dist (tag t x) (tag t y) ^ 2 = ∑ i : Fin m × Axis, (t * (x i.1 i.2 - y i.1 i.2 : ℤ))^2 := by
  rw [dist_eq_norm,← Points.flatten.norm_map,EuclideanSpace.real_norm_sq_eq]; simp only [map_sub,PiLp.sub_apply]
  refine Finset.sum_congr rfl fun i _ => ?_; change (_ * _ - _ * _) ^ 2 = _
  simp only [Int.cast_sub,mul_sub]

lemma extent {n : ℕ} (s : positions n) (k : Fin n) (i : Axis) (l : ℕ) (t : ℝ) (ht : 0 < t) :
    dist (tag t (advance s k i l)) (tag t s) = t*l := by
  apply (sq_eq_sq₀ dist_nonneg (by positivity)).1
  rw [norm_tag,Finset.sum_eq_single_of_mem (k,i) (Finset.mem_univ _)]
  · simp [advance]
  rintro ⟨j,b⟩ _ he; by_cases h : j=k
  · subst j; simp at he; simp [advance,he]
  simp [advance,h]

/-- A centered width cost for current word, each token and adjoints. -/
def Permit {n} (v : Fin n→C.book.Token) (A : ℝ) (e N p : ℕ) :=
    ∀ i w, (w=v i ∨ ∃ a, w=C.book.reflectedToken a (v i)) → centeredBudget C w A e N p

lemma permits {f} (h : CenteredBook C f) (p : ℕ) {n} (v : Fin n → C.book.Token) :
    (∀ᶠ m in atTop, ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ j in atTop, Permit v A m (f.mesh j) p) ∧
    (∀ᶠ m in atTop, ∃ A : ℝ, 0 ≤ A ∧ f.late (Permit v A m)) := by
  let I := Fin n ⊕ (Axis × Fin n)
  let P : I → C.book.Token := Sum.elim v fun i => C.book.reflectedToken i.1 (v i.2)
  letI : Fintype I := inferInstanceAs (Fintype (Fin n ⊕ (Axis × Fin n)))
  have ht := lib _ _ Finset.univ h p P
  have he (m N p T) (h : ∀ i∈Finset.univ, centeredBudget C (P i) T m N p) : Permit v T m N p := by
    rintro i w (rfl|⟨a,rfl⟩)
    · exact h (Sum.inl i) (Finset.mem_univ _)
    exact h (Sum.inr (a,i)) (Finset.mem_univ _)
  constructor
  · filter_upwards [ht.1] with m hm; obtain ⟨Q,hq,H⟩ := hm; exact ⟨Q,hq,H.mono fun i h => he _ _ _ _ h⟩
  filter_upwards [ht.2] with m hm; obtain ⟨Q,hq,H⟩ := hm; exact ⟨Q,hq,H.mono fun j h => h.mono fun i h => he _ _ _ _ h⟩

lemma stepTotal {m : ℕ} (H : C.Makes) (v : Fin (m+1)→C.book.Token) {A r : ℝ} (ha : 0 ≤ A)
    (hr : 0<r) (K : Set (Points (m+1))) (p N D : ℕ) (hd : D≤N) (h : Permit v A D N p)
    (he : ∀ x∈K, allFine C.S p (4*r) x) (hv : C.S.a D < r)
    (k : Fin (m+1)) (i : Axis) (l : ℕ) (u : positions (m+1))
    (hq : tag (C.S.a N) u ∈ K) (hb : dist (tag (C.S.a N) (advance u k i l)) (tag (C.S.a N) u) ≤ r) :
    dist (lifted C N p v (advance u k i l)) (lifted C N p v u) ≤
      (A^(m+1)/r)*dist (tag (C.S.a N) (advance u k i l)) (tag (C.S.a N) u) := by
  let L := (C.S.toDepth hd p).count.val
  let x := wrap (C.side N p) ∘ u
  let g := C.S.a N
  have hh := show 0<g from C.S.a_pos _
  rw [extent _ _ _ _ _ hh] at hb ⊢
  unfold Permit at h
  have hp : C.sufficient N v := by
    intro i; exact (h i (v i) (Or.inl rfl)).choose_spec.1
  cases Nat.eq_zero_or_pos m with
  | inl e =>
    subst m; rw [shifted]; change dist _ (C.numeric N p v x) ≤ _
    let t := offset i ((↑l:Per (C.side N p)))
    rw [show update (⇑(wrap _) ∘ u) k _= fun i : Fin (0+1) => x i + t by
      ext1 i; rw [@Subsingleton.elim (Fin 1) _ i k, Function.update_self];rfl, C.anchored H v hp t x,dist_self]
    exact mul_nonneg (div_nonneg (pow_nonneg ha _) hr.le) (mul_nonneg hh.le (Nat.cast_nonneg _))
  | inr e =>
    have hw : g*L=C.S.a D := C.S.embeds_scale (C.S.toDepth hd p)
    have ht (a b : Fin (m+1)) (hs:a≠b) : (2:ℝ)*L + 2*(r/g) < ((x b i - x a i).val:ℝ) := by
      have hz := gridAxis _ x rfl (he _ hq) _ _ hs i
      apply lt_of_mul_lt_mul_left _ hh.le
      calc
        g * ((2:ℝ)*L+2*(r/g)) = 2*(g*L)+2*r := by field_simp
        _ < 4*r := by linarith
        _ ≤ _ := hz
    have hf : (l:ℝ) ≤ r/g := (le_div_iff₀' hh).mpr hb
    have hu := primitive H i v hp hd L rfl (fun _ => A) e x (r/g) (div_pos hr hh) ht (fun j w hh => ?_) k l hf
    · rw [dist_eq_norm, shifted]
      apply hu.trans_eq
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
      ring_nf; simp [mul_comm,mul_left_comm]; ring
    obtain ⟨hD,_,hr⟩ := h j w (hh.imp_right fun p => ⟨i,p⟩); exact hr _

section
variable {n : ℕ} (x y : positions n)
private def via (s : Finset (Fin n × Axis)) (i : Fin n) (a : Axis) := if (i,a)∈s then x i a else y i a

private lemma replaces (t : ℝ) (s u : Finset (Fin n × Axis)) :
    dist (tag t (via x y s)) (tag t (via x y u)) ≤ dist (tag t x) (tag t y) := by
  apply (sq_le_sq₀ dist_nonneg dist_nonneg).1
  simp_rw [norm_tag]; apply Finset.sum_le_sum; intro p _
  unfold via; split_ifs <;> simp <;> first | rfl | positivity | ring_nf; rfl

private theorem comparable (h : C.Makes) {n : ℕ} (v : Fin (n+1) → C.book.Token)
    {A r t : ℝ} (ha : 0 ≤ A) (hr : 0<r) (K L : Set (Points (n+1))) (p N D : ℕ) (hd : D≤N) (H : Permit v A D N p)
    (he : ∀ y∈L, allFine C.S p (4*r) y) (hv : C.S.a D < r) (Ks : cthickening t K ⊆ L)
    (x y : positions (n+1)) (hy : tag (C.S.a N) y ∈ K)
    (hx : dist (tag (C.S.a N) x) (tag (C.S.a N) y) ≤ min r t) :
    dist (lifted C N p v x) (lifted C N p v y) ≤
      ((n+1:ℕ)* (4:ℝ)) *((A^(n+1)/r)*dist (tag (C.S.a N) x) (tag (C.S.a N) y)) := by
  let a := C.S.a N
  let E := A^(n+1)/r
  let R := dist (tag a x) (tag a y)
  let D' := lifted C N p v
  let W := via x y
  have hb (s u) : dist (tag a (W s)) (tag a (W u)) ≤ R := replaces x y a s u
  have hy' : W ∅=y := by ext; simp [W,via]
  have hR (s) : tag a (W s)∈L := Ks (mem_cthickening_of_dist_le _ _ _ K hy
    ((hy' ▸ hb s ∅ : dist (tag a (W s)) (tag a y) ≤ R).trans (hx.trans (min_le_right ..))))
  have he' : 0≤E := div_nonneg (pow_nonneg ha _) hr.le
  have ht {u v' : Finset (Fin (n+1) × Axis)} (i j l) (hk : W u = advance (W v') i j l) :
      dist (D' (W u)) (D' (W v')) ≤ E*R := by
    apply le_trans (show dist (D' (W u)) (D' (W v')) ≤ E * dist (tag a (W u)) (tag a (W v')) from by
      rw [hk]; refine stepTotal h v ha hr L p N D hd H he hv i j l (W v') (hR v') ?_
      exact hk ▸ (hb u v').trans (hx.trans (min_le_left ..))) (mul_le_mul_of_nonneg_left (hb u v') he')
  have hs (s) : dist (D' (W s)) (D' y) ≤ (s.card:ℝ)*(E*R) := by
    induction s using Finset.induction_on with
    | empty => simp [hy']
    | @insert b s hB ih =>
      obtain ⟨i,j⟩ := b
      rw [Finset.card_insert_of_notMem hB,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm ((s.card:ℝ)*_)]
      refine (dist_triangle _ (D' (W s)) _).trans (add_le_add ?_ ih)
      rcases le_total (x i j) (y i j) with h|h
      · rw [dist_comm]; apply ht i j (y i j-x i j).natAbs
        funext u w
        by_cases hu : u=i
        swap; simp [advance,W,via,hu]
        subst u
        by_cases hw : w=j
        · subst w
          simp only [advance,W,via, Function.update_self, hB,Finset.mem_insert_self, Pi.add_apply,Pi.smul_apply,
            ↓reduceIte, step_apply]; simp [abs_of_nonneg (sub_nonneg.mpr h)]
        · simp [advance,W,via,hw]
      apply ht i j (x i j-y i j).natAbs
      funext u w; by_cases hu : u=i
      · subst u; by_cases hw : w=j
        · subst w; simp [W,via,advance,hB,abs_of_nonneg (sub_nonneg.mpr h)]
        simp [W,via,advance,hw]
      simp [W,via,advance,hu]
  convert hs Finset.univ using 1
  · rw [show W Finset.univ=x by ext; simp [W,via]]
  simp only [Finset.card_univ,Fintype.card_prod,Axis,Fintype.card_fin, Nat.cast_mul,Nat.cast_ofNat];rfl
end

private lemma budget_epsilon {n : ℕ} (A r T ε : ℝ) (he : ε>0) (hr : 0<r) (hA : 0≤A) (hT : 0<T) :
    ∃ t : ℝ, 0<t ∧ t ≤ min r T ∧ ((↑(n+1:ℕ):ℝ)* (4:ℝ)) * ((A^(n+1)/r)*t) < ε := by
  let L := ((↑(n+1:ℕ):ℝ)* (4:ℝ)) * (A^(n+1)/r)
  have hL : 0≤L := by unfold L; positivity
  let t := min (min r T) (ε/(1+L))
  have ht : 0<t := by unfold t; exact lt_min (lt_min hr hT) (by positivity)
  refine ⟨t,ht,min_le_left ..,?_⟩
  rw [← mul_assoc]
  change L*t<ε
  calc
    _ < (1+L)*t := by linarith
    _ ≤ _ := (le_div_iff₀' (by linarith : 0<1+L)).mp (min_le_right ..)

/-- Two compact clauses, now genuinely supplied from *the exact* cell
estimates on one trajectory. -/
theorem completed (H : C.Makes) {f} (h : CenteredBook C f) : TransferLip C f := by
  constructor
  · intro p n K ht hK v ε hε
    cases n with
    | zero => exact ⟨1,zero_lt_one,Eventually.of_forall fun i b u _ _ _ => by rw [Subsingleton.elim b u, dist_self]; exact hε⟩
    | succ n =>
      obtain ⟨T,hT,hKT⟩ := ht.exists_cthickening_subset_open (cyclicOpen C.S p (n+1)) hK
      let M := cthickening T K
      obtain ⟨R,hR,hr⟩ := all _ _ (show IsCompact M from ht.cthickening) hKT
      obtain ⟨D,hD,hB⟩ := ((C.S.shrinks.eventually (gt_mem_nhds (by linarith : (0:ℝ)<R/4))).and (permits h p v).1).exists
      obtain ⟨A,hA,hv⟩ := hB
      obtain ⟨t,hy,hw,hf⟩ := budget_epsilon (n := n) A (R/4) T ε hε (by positivity) hA hT
      refine ⟨t,hy,?_⟩
      filter_upwards [hv, f.mesh.cofinal.eventually (eventually_ge_atTop D)] with i he hi b u hb hu Ht
      apply lt_of_le_of_lt (comparable H v hA (r := R/4) (by positivity) K M p _ D hi he (by
        rw [show (4:ℝ)*(R/4)=R by ring]; exact hr) hD (subset_refl (cthickening T K)) _ _ hu (Ht.le.trans hw))
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left Ht.le (by positivity)) (by positivity)) hf
  intro n K ht hk v ε hε
  cases n with
  | zero => exact ⟨1,zero_lt_one,Eventually.of_forall fun i => Eventually.of_forall fun j b u _ _ _ => by rw [Subsingleton.elim b u, dist_self]; exact hε⟩
  | succ n =>
    obtain ⟨T,hT,hKT⟩ := ht.exists_cthickening_subset_open (genericOpen _) hk
    let M := cthickening T K
    obtain ⟨R,hR,hr⟩ := allGrows C.S (show IsCompact M from ht.cthickening) hKT
    obtain ⟨D,hD,hB⟩ := ((C.S.shrinks.eventually (gt_mem_nhds (by linarith : (0:ℝ)<R/4))).and (permits h 0 v).2).exists
    obtain ⟨A,hA,hv⟩ := hB
    obtain ⟨t,hy,hw,hf⟩ := budget_epsilon (n := n) A (R/4) T ε hε (by positivity) hA hT
    refine ⟨t,hy,?_⟩
    unfold Order.late at hv ⊢
    filter_upwards [hv,f.per.cofinal.eventually hr] with i he hp
    filter_upwards [he, f.mesh.cofinal.eventually (eventually_ge_atTop D)] with j hh hi b u hb hu Ht
    apply lt_of_le_of_lt (comparable H v hA (r := R/4) (by positivity) K M (f.per i) _ D hi hh (by
      rw [show (4:ℝ)*(R/4)=R by ring]; exact hp) hD (subset_refl (cthickening T K)) _ _ hu (Ht.le.trans hw))
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left Ht.le (by positivity)) (by positivity)) hf
end YM.Extraction.Difference
