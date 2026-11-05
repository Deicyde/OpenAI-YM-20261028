import YM.TraceExtension.Verse.Pound

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
namespace YM.Trace.Verse
open Function Set Filter MeasureTheory Extraction Wilson Spec Cells Lattice Word Bid
open scoped Topology BigOperators

variable {G : Gauge} {C : Family G} {F : Filter (ℕ×ℕ)} {k b : ℕ}
variable (E : Scene C F k) {m : ℕ} (i : Fin (2*m) → Fin E.num)

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

def placeSlot (e : b ≤ k) (t : ℕ) (s : Slot E i) := E.seats (i s.1) s.2 + Scene.step C e t s.1.val

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
  unfold Scene.flick
  congr 2
  funext j
  by_cases h : j.val%2=0
  · simp only [h,if_true,carry,Word.conjugate,Scene.word,realize,List.map_ofFn,comp_def]
    apply congr_arg List.ofFn
    funext q
    simp only [Extraction.Order.grid,points_apply,Register.conjugate,f,placeSlot,gradeSlot,labelSlot,h,if_true,grid_add]
    rfl
  simp only [h,if_false,carry,Scene.word,realize,List.map_ofFn,comp_def]
  apply congr_arg List.ofFn
  funext q
  simp only [Extraction.Order.grid,points_apply,f,placeSlot,gradeSlot,labelSlot,h,if_false,grid_add]

lemma steps_apart (e : b ≤ k) {j l : ℕ} (hj : j ≠ l) (x y : ℤ) (a : Axis) :
    ∀ᶠ t : ℕ in atTop, x+Scene.step C e t j a ≠ y+Scene.step C e t l a := by
  by_cases hb : ∃ s : ℕ, x+Scene.step C e s j a = y+Scene.step C e s l a
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
      have he := add_right_cancel (show E.seats (i j) q a+Scene.step C e t j.val a = E.seats (i j) r a+_ from ht)
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

lemma nowSlot_limit (s : Slot E i) : Tendsto (fun c:ℕ×ℕ=> nowSlot E i s c.1 c.2) F (𝓝 (labelSlot E i s)) := by
  unfold nowSlot labelSlot
  split
  · exact (E.views _ s.2).star
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
    C.O N p (d := E.weight a q) v (location C.S k N p (E.seats a q+Scene.step C e t j.val)) U
  have h (j : Fin (2*m)) :
      (if j.val%2=0 then star (E.cuts N p (Scene.step C e t j.val) U) else E.cuts N p (Scene.step C e t j.val) U) =
        ∑ a, factor j a * monomial j a := by
    by_cases hj : j.val%2=0
    · simp only [hj,if_true,Scene.cuts,star_sum,star_mul',star_prod,factor,monomial]
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      exact Finset.prod_congr rfl fun q _ => (C.reality H (hN a q) _ _ _).symm
    simp only [hj, if_false, Scene.cuts,factor,monomial]
  unfold Scene.twice
  simp_rw [h]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.prod_mul_distrib,term,slotProd]
  rfl

lemma fromCut_expand (H : C.Makes) (e : b ≤ k) {f : Extraction.Order} (hf : F ≤ f.fuse) (m t : ℕ) :
    ∀ᶠ c : ℕ × ℕ in F, E.fromCut e t m c.1 c.2 =
      ∑ i, E.price m i * moment (C.beta c.1 c.2) (term E i e t c.1 c.2) := by
  have he : ∀ᶠ c : ℕ × ℕ in F, ∀ a q, C.ref (E.weight a q) ≤ c.1 :=
    eventually_all.mpr fun a => (Extraction.Order.witnesses (C:=C) (fun q => ⟨_,E.point a q⟩) f).filter_mono hf
  filter_upwards [he] with c hN
  dsimp only [Scene.fromCut, moment]
  simp_rw [twice_expand E H e m t c.1 c.2 hN]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  exact fun i _ => continuous_integrable (C.beta c.1 c.2) (continuous_const.mul (term_cont E i e t c.1 c.2))

lemma vary {S : Table C.book}{f: Extraction.Order} (hf:F ≤ f.fuse)(H : f.PointLimits C S)
    {n d} {u : Fin n→Cover}(hx:Extraction.Order.grid C k u ∈ generic _) (p:C.book.Vector d)(B:ℕ→ℕ→C.book.Vector (n:=n) d)
    (hB:∀ a, Tendsto (fun c:ℕ×ℕ=> B c.1 c.2 a) F (𝓝 (p a))) :
    Tendsto (fun c:ℕ×ℕ=> C.ensemble d (fun i=> location C.S k c.1 c.2 (u i)) (B c.1 c.2)) F (𝓝 (S.value d (Extraction.Order.grid C k u) p)):=by
  let E (i) := dial (L := C.book) d i
  let J := (i : Fin n) → (C.book.coord (d i)).Index
  letI : Fintype J := Pi.instFintype
  let Y (r : J) i := E i (r i)
  let W (F : C.book.Vector d) (r : J) := ∏ i, (E i).repr (F i) (r i)
  have he (X : Moment C.book n d) (t : C.book.Vector d) :
      X t = ∑ j : J, W t j * X (Y j) := by
    have hx : t = fun i => ∑ k, (E i).repr (t i) k • E i k :=
      funext fun i => ((E i).sum_repr _).symm
    conv_lhs => rw [hx]
    rw [MultilinearMap.map_sum]; apply Finset.sum_congr rfl
    exact fun i _ => X.map_smul_univ (fun k => (E k).repr (t k) (i k)) _
  have hh (v):Tendsto (fun c:ℕ×ℕ=> C.ensemble d (fun i=> location C.S k c.1 c.2 (u i)) v) F (𝓝 (S.value d (Extraction.Order.grid C k u) v)) :=
      (Extraction.Order.along (eventual_grid C f S H u hx (fun i=>⟨d i,v i⟩))).mono_left hf
  conv=> arg 1; intro c; rw [he]
  rw [he (S.value ..) p]
  apply tendsto_finsetSum _; intro j hj
  refine Tendsto.mul ?_ (hh _)
  exact tendsto_finsetProd _ fun i _=> (((E i).coord (j i)).continuous_of_finiteDimensional.continuousAt.tendsto.comp (hB i))

lemma term_pass {S : Table C.book} {f: Extraction.Order} (hf:F ≤ f.fuse)(H : f.PointLimits C S) (e : b ≤ k) : ∀ᶠ t : ℕ in atTop,
    Tendsto (fun c : ℕ × ℕ => moment (C.beta c.1 c.2) (term E i e t c.1 c.2)) F
      (𝓝 (S.expect (E.flick e t m i))) := by
  filter_upwards [translate_generic E i e] with t ht
  rw [flick_realized E i e t, Table.readAt]
  exact vary hf H ht (fun a=> labelSlot E i ((slots E i).get a)) (fun N p a=> nowSlot E i ((slots E i).get a) N p) (fun a=> nowSlot_limit E i ((slots E i).get a))
end YM.Trace.Verse
