import YM.Next.PHASE.Passage
import YM.OS.Halves


/-!
# Pricing the train Gram from the mixed cell estimate

Full reflected copies. There are just two main point patterns per slot (along
time, integral slab width at the chosen cell scale). The two exterior copies
need not fit the main-field margin; charge them to the exterior scale. No
positive arity condition in this part. Constants are paid independently of
how many replicas are being passed to the continuum.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Phase
open Function Set Filter Extraction OS Word
open scoped NNReal Topology BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {L : Register G} {r t : ℝ} {d e : ℝ≥0} {u v : L.Word}

-- Membership-based spacing bookkeeping (use separately from Word.distinct).
private def apart (r : ℝ) (w : L.Word) :=
  ∀ x ∈ w, ∀ y ∈ w, x≠y → r ≤ cubedist x.1 y.1

private lemma from_buffer (h : buffer timeAxis r d u) : apart r u := by
  intro x hx y hy he
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hx
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hy
  exact h.1 i j fun p => he (congrArg _ p)

private lemma apart_raise (h : apart r u) (d : ℝ≥0) : apart r (raised timeAxis d u) := by
  intro x hx y hy he
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hy
  dsimp only
  unfold cubedist; rw [WithLp.ofLp_add,WithLp.ofLp_add,dist_add_right]
  exact h _ hp _ hq (fun h => he (h ▸ rfl))

private lemma reflect_dist (x y : E4) : cubedist (Ortho.move (Signed.reflect timeAxis) x)
    (Ortho.move (Signed.reflect timeAxis) y)=cubedist x y := by
  unfold cubedist
  have he i : dist (Ortho.move (Signed.reflect timeAxis) x i) (Ortho.move (Signed.reflect timeAxis) y i) =
      dist (x i) (y i) := by by_cases h : i=timeAxis <;> simp [h]
  apply le_antisymm <;> apply (dist_pi_le_iff dist_nonneg).mpr <;> intro i
  · rw [he]; exact dist_le_pi_dist ..
  rw [← he]; exact dist_le_pi_dist ..

private lemma apart_reflect (h : apart r u) : apart r (reflect u timeAxis) := by
  intro x hx y hy he
  rw [reflectedPoint] at hx hy
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hy
  dsimp only; rw [reflect_dist]
  exact h _ (List.mem_reverse.mp hp) _ (List.mem_reverse.mp hq) (fun h => he (h ▸ rfl))

private lemma apart_join (hu : apart r u) (hv : apart r v)
    (h : ∀ x ∈ u, ∀ y ∈ v, r ≤ cubedist x.1 y.1) : apart r (u++v) := by
  intro x hx y hy he
  rcases List.mem_append.mp hx with p|p <;> rcases List.mem_append.mp hy with q|q
  · exact hu _ p _ q he
  · exact h _ p _ q
  · rw [show cubedist x.1 y.1=cubedist y.1 x.1 from dist_comm ..]; exact h _ q _ p
  exact hv _ p _ q he

private lemma gap_time (x y : E4) (h : r ≤ y timeAxis-x timeAxis) : r ≤ cubedist x y := by
  have hr : dist (x timeAxis) (y timeAxis) ≤ cubedist x y := dist_le_pi_dist ..
  rw [dist_comm,Real.dist_eq] at hr; exact h.trans ((le_abs_self _).trans hr)

private def limits (r : ℝ) (d : ℝ≥0) (u : L.Word) :=
  apart r u ∧ ∀ p∈u, r ≤ p.1 timeAxis ∧ p.1 timeAxis ≤ (d:ℝ)-r

private lemma across_link (hr : 0 ≤ r) (x : limits r d u) (y : limits r e v) :
    limits r (d+e) (linked timeAxis d u v) := by
  constructor
  · apply apart_join x.1 (apart_raise y.1 d)
    intro p hp q hq
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hq
    have hw := (x.2 p hp).2; have he := (y.2 s hs).1
    apply gap_time
    change r ≤ (s.1 + (d:ℝ) • basis _) timeAxis - _; simp; linarith
  intro p hp
  rcases List.mem_append.mp hp with h|h
  · obtain ⟨H,j⟩ := x.2 p h; refine ⟨H,j.trans ?_⟩; simp
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp h
  obtain ⟨he,hh⟩ := y.2 s hs; simp; constructor <;> linarith [show (0:ℝ) ≤ (d:ℝ) from d.property]

private lemma across_mirror (x : limits r d u) : limits r d (opposite timeAxis d u) := by
  refine ⟨apart_raise (apart_reflect x.1) _,?_⟩
  intro p hp; obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hp
  rw [reflectedPoint] at hs; obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hs
  obtain ⟨h,w⟩ := x.2 t (List.mem_reverse.mp ht)
  simp; constructor <;> linarith

private def train (d : ℝ≥0) (w : L.Word) : ℕ → L.Word :=
  Nat.rec ([] : L.Word) (fun _ => linked timeAxis (d+d) (linked timeAxis d (opposite timeAxis d w) w))
private lemma train_zero (w : L.Word) : train d w 0 = [] := rfl
private lemma train_next (w : L.Word) (q : ℕ) :
    train d w (q+1)=linked timeAxis (d+d) (linked timeAxis d (opposite timeAxis d w) w) (train d w q) := rfl

private def ends (d : ℝ≥0) (q : ℕ) := (d+d)*q
private lemma ends_next (q : ℕ) : ends d (q+1)=d+d+ends d q := by unfold ends; push_cast; ring

private lemma train_buffer (q) (hr : 0 ≤ r) (hb : buffer timeAxis r d u) : limits r (ends d q) (train d u q) := by
  induction q with
  | zero => simp [train_zero,limits,apart]
  | succ q ih =>
    have he : limits r d u := ⟨from_buffer hb,hb.2⟩
    rw [train_next,ends_next]; exact across_link hr (across_link hr (across_mirror he) he) ih

private lemma train_length (w : L.Word) (q : ℕ) : (train d w q).length = 2*q*w.length := by
  induction q with
  | zero => simp [train_zero]
  | succ q ih =>
    rw [train_next]
    simp only [linked,List.length_append,opposite,raised,carry,List.length_map,reflectedPoint,
      List.length_reverse,ih]; ring

private lemma ride_train (H : Slab timeAxis d u) (v : Future L timeAxis) (q) :
    (ride H v q).val = train d u q ++ raised timeAxis (ends d q) v.val := by
  induction q with
  | zero => simp [ride,train_zero,raised,ends]
  | succ q ih =>
    rw [ride,iterate_succ_apply']
    change (entering (mirrorsSlab H) (entering H (ride H v q))).val=_
    change linked timeAxis _ _ (linked timeAxis _ _ (ride H v q).val)=_
    rw [ih,train_next,ends_next]
    simp only [linked, raised, distribute, paths, NNReal.coe_add,add_smul,List.append_assoc]
    abel_nf

private def twins (w : L.Word) := reflect w timeAxis ++ w

private lemma pair_length (w : L.Word) : (twins w).length = 2*w.length := by simp [twins,two_mul]

private lemma pair_gap (hr : 0 ≤ r) (h : apart r u) (ht : ∀ p∈u, r ≤ p.1 timeAxis) : apart r (twins u) := by
  apply apart_join (apart_reflect h) h
  intro p hp q hq; rw [reflectedPoint] at hp
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hp
  have he := ht s (List.mem_reverse.mp hs); have hh := ht q hq
  apply gap_time; simp; linarith

private lemma exterior_gap (v : L.Word) (b : buffer timeAxis t e v) (ht : 0 ≤ t) (d) :
    apart t (twins (raised timeAxis d v)) := by
  apply pair_gap ht (apart_raise (from_buffer b) d); intro x hx
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
  have hh := (b.2 p hp).1; simp; linarith [show (0:ℝ) ≤ (d:ℝ) from d.property]

private lemma cross_gap (v : Future L timeAxis) (hr : 0 ≤ r) (hx : limits r d u) (x) (h : x ∈ twins u) (y)
    (he : y ∈ twins (raised timeAxis d v.val)) : r ≤ cubedist x.1 y.1 := by
  have hm : -(d:ℝ) + r ≤ x.1 timeAxis ∧ x.1 timeAxis ≤ (d:ℝ)-r := by
    rcases List.mem_append.mp h with h|h
    · rw [reflectedPoint] at h; obtain ⟨s,hs,rfl⟩ := List.mem_map.mp h
      obtain ⟨ha,hb⟩ := hx.2 _ (List.mem_reverse.mp hs)
      simp; constructor <;> linarith
    obtain ⟨ha,hb⟩ := hx.2 x h; constructor <;> linarith [d.property]
  have hl (p) (hp : p∈raised timeAxis d v.val) : (d:ℝ) ≤ p.1 timeAxis := by
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    have hv := v.property.2 _ hq; simp; linarith
  rcases List.mem_append.mp he with h|h
  · rw [reflectedPoint] at h; obtain ⟨s,hs,rfl⟩ := List.mem_map.mp h
    have hv := hl _ (List.mem_reverse.mp hs)
    have hx : r ≤ x.1 timeAxis - Ortho.move (Signed.reflect timeAxis) s.1 timeAxis := by simp; linarith [hm.1]
    exact (gap_time _ _ hx).trans_eq (dist_comm ..)
  have hv := hl _ h; exact gap_time _ _ (by linarith [hm.2])

private lemma train_twins (h : Slab timeAxis d u) (v : Future L timeAxis) (q : ℕ) :
    List.Perm (twins (ride h v q).val) (twins (train d u q) ++ twins (raised timeAxis (ends d q) v.val)) := by
  rw [ride_train]; let s := train d u q; let w := raised timeAxis (ends d q) v.val
  change List.Perm (reflect (s++w) _ ++ (s++w)) (twins s ++ twins w)
  have hp : List.Perm (reflect w timeAxis ++ twins s) (twins s ++ reflect w timeAxis) := List.perm_append_comm
  simpa [twins,List.append_assoc] using hp.append_right w

private def suit (s : ℝ) (w u : L.Word) := ∀ p∈u, ∃ y∈twins w, Pattern s p.1 y.1 ∧ p.2=y.2

private lemma suit_init (w : L.Word) (s : ℝ) : suit s w w ∧ suit s w (reflect w timeAxis) := by
  have he x (h : x∈twins w) : ∃ y∈twins w, Pattern s x.1 y.1 ∧ x.2=y.2 := ⟨_,h,fun a => ⟨0,by simp⟩,rfl⟩
  exact ⟨fun x h => he _ (List.mem_append_right _ h),fun x h => he _ (List.mem_append_left _ h)⟩

private lemma suit_raise (s : ℝ) (h : suit s u v) (l : ℕ) (hh : (d:ℝ) = l*s) : suit s u (raised timeAxis d v) := by
  intro x hx; obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
  obtain ⟨y,hy,H,K⟩ := h p hp
  refine ⟨y,hy,fun a => ?_,K⟩
  obtain ⟨z,hz⟩ := H a
  by_cases ha : a=timeAxis
  · refine ⟨z+l,?_⟩; subst a; simp [hz,hh]; ring
  exact ⟨z,by simp [ha,hz]⟩

private lemma train_suit {m : ℕ} (S : Schedule) (w : L.Word) (h : Covered S d m) (q : ℕ) :
    suit (S.a m) w (train d w q) := by
  obtain ⟨l,hl⟩ := h
  induction q with
  | zero => simp [suit,train_zero]
  | succ q ih =>
    have ht := suit_init w (S.a m)
    intro p hp
    rw [train_next] at hp
    rcases List.mem_append.mp hp with hx|hx
    · rcases List.mem_append.mp hx with hx|hx
      · exact suit_raise _ ht.2 _ hl p hx
      exact suit_raise _ ht.1 _ hl p hx
    exact suit_raise (d:=d+d) _ ih (l+l) (by push_cast; rw [hl]; ring) p hx

private lemma suit_pairs (s : ℝ) (h : suit s u v) : suit s u (twins v) := by
  intro p hp; rcases List.mem_append.mp hp with hv|hv
  · rw [reflectedPoint] at hv; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
    obtain ⟨y,hy,H,K⟩ := h _ (List.mem_reverse.mp hx)
    refine ⟨(Ortho.move (Signed.reflect timeAxis) y.1,L.reflectedToken timeAxis y.2),?_,fun a => ?_,
      congrArg (L.reflectedToken timeAxis) K⟩
    · rcases List.mem_append.mp hy with h₁|h₂
      · apply List.mem_append_right
        have hh : (Ortho.move (Signed.reflect timeAxis) y.1,L.reflectedToken timeAxis y.2) ∈ reflect (reflect u timeAxis) timeAxis := by
          rw [reflectedPoint]; exact List.mem_map.mpr ⟨_,List.mem_reverse.mpr h₁,rfl⟩
        rw [reflect_twice] at hh; exact hh
      apply List.mem_append_left; rw [reflectedPoint]; exact List.mem_map.mpr ⟨_,List.mem_reverse.mpr h₂,rfl⟩
    obtain ⟨b,hb⟩ := H a; by_cases ha : a=timeAxis
    · refine ⟨-b,?_⟩; subst a; simp [hb]; ring
    exact ⟨b,by simp [ha,hb]⟩
  exact h p hv

private lemma pair_rep {C : Family G} (F : Extraction.Order) (w : C.book.Word) (A : ℝ) (b : ℕ)
    (H : ∀ p∈w, F.late (Single C p.2 A b)) : ∀ p∈twins w, F.late (Single C p.2 A b) := by
  intro p hp; rcases List.mem_append.mp hp with he|he
  · rw [reflectedPoint] at he; obtain ⟨y,hy,rfl⟩ := List.mem_map.mp he
    apply (H _ (List.mem_reverse.mp hy)).mono
    intro i h; apply h.mono; intro j hi
    have ht : C.book.reflectedToken timeAxis y.2 = Spin.token C.book y.2 (Signed.mirror timeAxis,true) := by
      simp only [← Register.token_adjoint, Spin.token,↓reduceIte, Extraction.Spin.swapC]
    change Single C (C.book.reflectedToken timeAxis y.2) _ _ _ _
    rw [ht]; exact hi.moves _
  exact H p he

private lemma words_bound {G : Gauge} {C : Family G} (H : C.Makes) (F : Order) (S : Table C.book) (ht : S.Smooth)
    (he : F.PointLimits C S) (m k l b : ℕ) (hm : m≤k) (hk : k≤l) (hl : l≤b)
    (u v : C.book.Word) (hc : distinct (u++v))
    (r t : ℝ) (hp : C.S.a m < r) (hh : C.S.a l < t)
    (hx : apart r u) (hy : apart t v) (hz : ∀ x∈u, ∀ y∈v, r ≤ cubedist x.1 y.1)
    (w : C.book.Word) (h : suit (C.S.a m) w u)
    (headroom : (↑(2*w.length : ℕ):ℝ)*(2*(5*C.S.a k)) < C.S.a m)
    (side : (v.length : ℝ)*(2*(3*C.S.a b)) < C.S.a l)
    (A B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ i∈w, F.late (Single C i.2 A k))
    (hf : ∀ j∈v, F.late (Single C j.2 B b)) :
    ‖S.expect (u++v)‖ ≤ A ^ u.length * B ^ v.length := by
  let e : Fin u.length ⊕ Fin v.length ≃ Fin (u.length+v.length) := finSumFinEquiv
  let x := composite u v 0
  let i := Fin.append (tokens u) (tokens v)
  have ht₀ : u++v=realize i x := by simpa only [rest] using placements u v 0
  have hb₀ : x∈conf _ := (realized ..).mp (ht₀ ▸ hc)
  have hu p : x (e (Sum.inl p))=(u.get p).1 := by simp [x,composite,e,positions,List.get_eq_getElem]
  have hv p : x (e (Sum.inr p))=(v.get p).1 := by simp [x,composite,e,positions,List.get_eq_getElem]
  have huu p : i (e (Sum.inl p))=(u.get p).2 := by simp [i,tokens,e,List.get_eq_getElem]
  have hvv p : i (e (Sum.inr p))=(v.get p).2 := by simp [i,tokens,e,List.get_eq_getElem]
  rw [ht₀,S.readAt]
  apply le_trans (point_bound e C H F S ht he m k l b hm hk hl x hb₀ i ?_ (twins w).length
    (positions (twins w)) ?_ (by rw [pair_length]; exact headroom) (by simpa using side) A B hB ?_ ?_) (le_of_eq (by simp))
  · refine ⟨fun p q hg => ?_, fun p q => ?_, fun p q hg => ?_⟩
    · rw [hu,hu]; refine hp.trans_le (hx _ (List.get_mem ..) _ (List.get_mem ..) fun h => hg ?_)
      have hhx : x (e (Sum.inl p)) = x (e (Sum.inl q)) := by rw [hu,hu,h]
      exact Sum.inl.inj (e.injective ((show Function.Injective _ from hb₀) hhx))
    · rw [hu,hv]; exact hp.trans_le (hz _ (List.get_mem ..) _ (List.get_mem ..))
    rw [hv,hv]; refine hh.trans_le (hy _ (List.get_mem ..) _ (List.get_mem ..) fun h => hg ?_)
    have hhx : x (e (Sum.inr p)) = x (e (Sum.inr q)) := by rw [hv,hv,h]
    exact Sum.inr.inj (e.injective ((show Function.Injective _ from hb₀) hhx))
  · intro p; obtain ⟨z,H,hz,-⟩ := h (u.get p) (List.get_mem ..)
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp H; rw [hu]; exact ⟨j,hz⟩
  · intro p; rw [huu]; obtain ⟨y,hy,-,hQ⟩ := h (u.get p) (List.get_mem ..)
    rw [hQ]; exact pair_rep F w A k ha y hy
  intro p; rw [hvv]; exact hf _ (List.get_mem ..)

/-- `A`,`B` pay, respectively, for each main and each exterior insertion. Uses
*all* `4*q` copies of the main word in this train and gives the required
 exterior cost independent of `q`. -/
theorem travel_price {C : Family G} (H : C.Makes) (F : Order) (S : Table C.book) (hs : S.Hierarchy)
    (he : F.PointLimits C S) {m k l b : ℕ} (hm : m≤k) (hk : k≤l) (hl : l≤b)
    {w : C.book.Word} (h : Slab timeAxis d w) (hd : buffer timeAxis r d w) (hc : Covered C.S d m)
    (v : Future C.book timeAxis) (hv : buffer timeAxis t e v.val) (q : ℕ)
    (hp : C.S.a m < r) (hh : C.S.a l < t)
    (headroom : (↑(2*w.length : ℕ):ℝ)*(2*(5*C.S.a k)) < C.S.a m)
    (side : (↑(2*v.val.length : ℕ):ℝ)*(2*(3*C.S.a b)) < C.S.a l)
    (A B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ i∈w, F.late (Single C i.2 A k))
    (hf : ∀ j∈v.val, F.late (Single C j.2 B b)) :
    ‖S.gram timeAxis (ride h v q).val (ride h v q).val‖ ≤ B ^ (2*v.val.length) * A ^ (w.length*(4*q)) := by
  let a := train d w q
  let x := twins a
  let p := raised timeAxis (ends d q) v.val
  let y := twins p
  have hperm : List.Perm (twins (ride h v q).val) (x++y) := train_twins ..
  have ht₀ : distinct (twins (ride h v q).val) := twoSides (ride h v q).property (ride h v q).property
  have ht : distinct (x++y) := locations.mpr ((hperm.map Prod.fst).nodup (locations.mp ht₀))
  have hr := ((C.S.a_pos m).trans hp).le
  have hxy : limits r (ends d q) a := train_buffer q hr hd
  change ‖S.expect (twins (ride h v q).val)‖ ≤ _
  rw [← S.order hs.laws.toSymmetric ht₀ hperm]
  have hil : y.length=2*v.val.length := by unfold y; rw [pair_length]; simp [p,raised,carry]
  calc
    _ ≤ A ^ x.length * B ^ y.length :=
      words_bound H F S hs.smooth he m k l b hm hk hl x y ht r t hp hh
        (pair_gap hr hxy.1 (fun p hp => (hxy.2 p hp).1))
        (exterior_gap _ hv ((C.S.a_pos l).trans hh).le _)
        (cross_gap v hr hxy) w (suit_pairs _ (train_suit _ w hc q)) headroom (by rw [hil]; exact side) A B hB ha
        (pair_rep F p B b (by
          intro i hi; obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hi; exact hf t ht))
    _ = _ := by unfold x a; rw [pair_length,train_length,hil, mul_comm]; ring
end YM.Next.Phase
