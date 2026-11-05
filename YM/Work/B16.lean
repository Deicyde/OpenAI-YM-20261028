import YM.Bid.Fetch

/-!
# Passage to finite polynomial limits in a fixed train

Flatten the array of slots in *list order* for each monomial choice (including
empty words) so the ensemble and the hierarchy use exactly the same grid and
cap. Coordinate ties between different packets have at most one bad translate
parameter per component/pair. Ordinary stars on cutoff fields can be realized
by ordinary label conjugation once their fixed reference levels fit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.B16
open Function Set Filter MeasureTheory Extraction Wilson Spec Cells Lattice Word Bid
open scoped Topology BigOperators

variable {G : Gauge} {C : Family G} {F : Extraction.Order} {k b : ℕ}
variable (E : Episode C F k) {m : ℕ} (i : Fin (2*m) → Fin E.num)

abbrev Slot := (j : Fin (2*m)) × Fin (E.image (i j))

def slots : List (Slot E i) := (List.ofFn fun j => List.ofFn fun q => (⟨j,q⟩ : Slot E i)).flatten

lemma slots_inj : Injective (slots E i).get := by
  apply List.nodup_iff_injective_get.mp
  apply List.pairwise_flatten.mpr
  constructor
  · intro l hl
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hl
    change List.Nodup _
    apply List.nodup_ofFn.mpr
    intro x y h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  apply List.pairwise_ofFn.mpr
  intro j q hj a ha b hb
  obtain ⟨u,rfl⟩ := List.mem_ofFn.mp ha
  obtain ⟨w,rfl⟩ := List.mem_ofFn.mp hb
  exact fun e => hj.ne (Sigma.mk.inj_iff.mp e).1

lemma slotProd (f : Slot E i → ℂ) :
    ∏ a, f ((slots E i).get a) = ∏ j, ∏ q, f ⟨j,q⟩ := by
  change ∏ a, (f ∘ (slots E i).get) a = _
  rw [← List.prod_ofFn, ← List.map_ofFn, List.ofFn_get]
  simp only [slots,List.map_flatten,List.prod_flatten,List.map_ofFn,comp_def,List.prod_ofFn]

def placeSlot (e : b ≤ k) (t : ℕ) (s : Slot E i) := E.seats (i s.1) s.2 + Episode.step C e t s.1.val

def gradeSlot (s : Slot E i) := E.weight (i s.1) s.2

def labelSlot (s : Slot E i) : C.label (gradeSlot E i s) :=
  if s.1.val % 2 = 0 then star (E.point (i s.1) s.2) else E.point (i s.1) s.2

def nowSlot (s : Slot E i) (N p : ℕ) : C.label (gradeSlot E i s) :=
  if s.1.val % 2 = 0 then star (E.current (i s.1) s.2 N p) else E.current (i s.1) s.2 N p

lemma grid_add (x y : Cover) : C.S.gridPoint k (x+y) = C.S.gridPoint k x+C.S.gridPoint k y := by
  apply PiLp.ext; intro a
  change C.S.a k * ((x a + y a : ℤ) : ℝ) = C.S.a k * (x a : ℝ) + C.S.a k * (y a : ℝ)
  simp only [Int.cast_add,mul_add]

lemma flick_realized (e : b ≤ k) (t : ℕ) : E.flick e t m i =
    realize (fun a => ⟨gradeSlot E i ((slots E i).get a),labelSlot E i ((slots E i).get a)⟩)
      (Extraction.Order.grid C k (fun a => placeSlot E i e t ((slots E i).get a))) := by
  let f (s : Slot E i) : C.book.Plant := (C.S.gridPoint k (placeSlot E i e t s), ⟨gradeSlot E i s,labelSlot E i s⟩)
  change _ = List.ofFn (f ∘ (slots E i).get)
  rw [← List.map_ofFn,List.ofFn_get, slots, List.map_flatten,List.map_ofFn]
  unfold Episode.flick
  congr 2
  funext j
  by_cases h : j.val%2=0
  · simp only [h,if_true,carry,Word.conjugate,Episode.word,realize,List.map_ofFn,comp_def]
    apply congr_arg List.ofFn
    funext q
    simp only [Extraction.Order.grid,points_apply,Register.conjugate,f,placeSlot,gradeSlot,labelSlot,h,if_true,grid_add]
    rfl
  simp only [h,if_false,carry,Episode.word,realize,List.map_ofFn,comp_def]
  apply congr_arg List.ofFn
  funext q
  simp only [Extraction.Order.grid,points_apply,f,placeSlot,gradeSlot,labelSlot,h,if_false,grid_add]

lemma steps_apart (e : b ≤ k) {j l : ℕ} (hj : j ≠ l) (x y : ℤ) (a : Axis) :
    ∀ᶠ t : ℕ in atTop, x+Episode.step C e t j a ≠ y+Episode.step C e t l a := by
  by_cases hb : ∃ s : ℕ, x+Episode.step C e s j a = y+Episode.step C e s l a
  · obtain ⟨s,hs⟩ := hb
    filter_upwards [eventually_gt_atTop s] with t ht
    intro he
    let D := (C.S.toDepth e 0).count.val
    have hD : 0 < (D : ℤ) := by exact_mod_cast (C.S.toDepth e 0).count.property
    change x+(↑(D*(2*s*j)) : ℤ) = y+↑(D*(2*s*l)) at hs
    change x+(↑(D*(2*t*j)) : ℤ) = y+↑(D*(2*t*l)) at he
    push_cast at hs he
    have hn : (((D : ℤ)*2)*((j : ℤ)-l))*((t : ℤ)-s) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (by positivity) (sub_ne_zero.mpr ?_)) (sub_ne_zero.mpr ?_)
      · exact_mod_cast hj
      exact_mod_cast ht.ne'
    exact hn (by linarith)
  exact Eventually.of_forall fun t h => hb ⟨t,h⟩

lemma translate_generic (e : b ≤ k) : ∀ᶠ t : ℕ in atTop,
    Extraction.Order.grid C k (fun a => placeSlot E i e t ((slots E i).get a)) ∈ generic _ := by
  have aux : ∀ᶠ t : ℕ in atTop, ∀ a : Axis, ∀ s u : Slot E i,
      (placeSlot E i e t s) a = (placeSlot E i e t u) a → s = u := by
    refine eventually_all.mpr fun a => eventually_all.mpr fun ⟨j,q⟩ => eventually_all.mpr fun ⟨l,r⟩ => ?_
    by_cases h : j = l
    · subst l
      apply Eventually.of_forall
      intro t ht
      have he := add_right_cancel (show E.seats (i j) q a+Episode.step C e t j.val a = E.seats (i j) r a+_ from ht)
      have hg : q = r := E.gen (i j) a (congr_arg (fun z : ℤ => C.S.a k * z) he)
      exact congr_arg (fun x => (⟨j,x⟩ : Slot E i)) hg
    filter_upwards [steps_apart (C:=C) e (show j.val ≠ l.val from fun h' => h (Fin.ext h'))
      (E.seats (i j) q a) (E.seats (i l) r a) a] with t ht
    exact fun he => (ht he).elim
  filter_upwards [aux] with t ht
  intro a x y hxy
  apply slots_inj E i
  apply ht a
  exact_mod_cast mul_left_cancel₀ (C.S.a_pos k).ne' (show
    C.S.a k * ((placeSlot E i e t ((slots E i).get x)) a : ℝ) =
      C.S.a k * ((placeSlot E i e t ((slots E i).get y)) a : ℝ) from hxy)

lemma nowSlot_limit (s : Slot E i) : F.limits (fun _ => True) (nowSlot E i s) (labelSlot E i s) := by
  unfold nowSlot labelSlot
  split
  · obtain ⟨hp,v,hv,hs⟩ := E.views _ s.2
    exact ⟨hp,fun p => star (v p),fun p ht => (hv p ht).star,hs.star⟩
  exact E.views _ _

def slotObs (e : b ≤ k) (t N p : ℕ) (U : Config G (C.side N p)) (s : Slot E i) :=
  C.O N p (d := gradeSlot E i s) (nowSlot E i s N p) (location C.S k N p (placeSlot E i e t s)) U

def term (e : b ≤ k) (t N p : ℕ) (U : Config G (C.side N p)) :=
  ∏ a, slotObs E i e t N p U ((slots E i).get a)

lemma term_cont (e : b ≤ k) (t N p : ℕ) : Continuous (term E i e t N p) :=
  continuous_finsetProd _ fun _ _ => C.continuousO _ _ _ _ _

lemma twice_expand (H : C.Makes) (e : b ≤ k) (m t N p : ℕ) (hN : ∀ a q, C.ref (E.weight a q) ≤ N)
    (U : Config G (C.side N p)) : E.twice e t m N p U = ∑ i, E.price m i * term E i e t N p U := by
  let factor (j : Fin (2*m)) (a : Fin E.num) := if j.val%2=0 then star (E.factor a) else E.factor a
  let monomial (j : Fin (2*m)) (a : Fin E.num) := ∏ q : Fin (E.image a),
    let v := if j.val%2=0 then star (E.current a q N p) else E.current a q N p
    C.O N p (d := E.weight a q) v (location C.S k N p (E.seats a q+Episode.step C e t j.val)) U
  have h (j : Fin (2*m)) :
      (if j.val%2=0 then star (E.cuts N p (Episode.step C e t j.val) U) else E.cuts N p (Episode.step C e t j.val) U) =
        ∑ a, factor j a * monomial j a := by
    by_cases hj : j.val%2=0
    · simp only [hj,if_true,Episode.cuts,star_sum,star_mul',star_prod,factor,monomial]
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      exact Finset.prod_congr rfl fun q _ => (C.reality H (hN a q) _ _ _).symm
    simp only [hj, if_false, Episode.cuts,factor,monomial]
  unfold Episode.twice
  simp_rw [h]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.prod_mul_distrib,term,slotProd]
  rfl

lemma fromCut_expand (H : C.Makes) (e : b ≤ k) (m t : ℕ) :
    ∀ᶠ c : ℕ × ℕ in F.fuse, E.fromCut e t m c.1 c.2 =
      ∑ i, E.price m i * moment (C.beta c.1 c.2) (term E i e t c.1 c.2) := by
  have he : ∀ᶠ c : ℕ × ℕ in F.fuse, ∀ a q, C.ref (E.weight a q) ≤ c.1 :=
    eventually_all.mpr fun a => Extraction.Order.witnesses (C:=C) (fun q => ⟨_,E.point a q⟩) F
  filter_upwards [he] with c hN
  dsimp only [Episode.fromCut, moment]
  simp_rw [twice_expand E H e m t c.1 c.2 hN]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  exact fun i _ => continuous_integrable (C.beta c.1 c.2) (continuous_const.mul (term_cont E i e t c.1 c.2))

lemma term_pass {S : Table C.book} (H : F.PointLimits C S) (e : b ≤ k) : ∀ᶠ t : ℕ in atTop,
    Tendsto (fun c : ℕ × ℕ => moment (C.beta c.1 c.2) (term E i e t c.1 c.2)) F.fuse
      (𝓝 (S.expect (E.flick e t m i))) := by
  filter_upwards [translate_generic E i e] with t ht
  rw [flick_realized E i e t, Table.readAt]
  have hL := Extraction.Order.along (keeps_moments C F S (fun a => placeSlot E i e t ((slots E i).get a)) ht H
    (d := fun a => gradeSlot E i ((slots E i).get a)) (fun a => labelSlot E i ((slots E i).get a))
    (fun N p a => nowSlot E i ((slots E i).get a) N p) (fun a => nowSlot_limit E i ((slots E i).get a)))
  exact hL

theorem answer : YM.Bid.B16 := by
  intro G C F S seed k b e E m
  filter_upwards [eventually_all.mpr (fun i : Fin (2*m) → Fin E.num => term_pass E i seed.generic e)] with t ht
  unfold Episode.wanted
  apply Tendsto.congr' ((fromCut_expand E seed.cutoff e m t).mono fun _ hc => hc.symm)
  exact tendsto_finsetSum _ fun i _ => tendsto_const_nhds.mul (ht i)

-- Empty train (even for an Episode with no available terms).


end YM.Work.B16
