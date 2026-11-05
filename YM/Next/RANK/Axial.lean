import YM.Tree.Cut


/-!
# A determinant budget on the actual torus: plaquette order

Rank comparison needs a *per replica* estimate on a terminal torus. A per-site loss
proportional to log β even after taking that root would be costly.  proposes
a gauge count (not an infinite-volume or vanishing-harmonics determinant estimate!).
Here is an explicit torus version with wraps. Sites have 4 coordinates in `ZMod L`.

Tree: children return home in the highest-numbered nonzero coordinate. Free bonds
live in tiers. In tier `i`, either a transverse bond sits in a nonzero slice of
axis `i`, or this is a wrap bond of axis `i`. Sweep tiers down; in each do the
wrap bonds *first*, except that one at the 'handle' is left out. Then sweep
transverse bonds from higher heights to lower. Tree and handles are held fixed
through the sweep. We prove a triangularity statement in terms of the actual four
edges of each used plaquette.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Next.Rank.Axial
open Lattice Tree Function Set
open scoped BigOperators

variable {L : Side}

def whole (L : Side) : Ratio 1 L := ⟨L, by simp⟩

private lemma node (x : Site L) : leaf (whole L) x ↔ x ≠ 0 := by
  haveI : Subsingleton (Site (1:Side)) := inferInstanceAs (Subsingleton (Axis → ZMod 1))
  unfold leaf
  simp only [Subsingleton.elim ((whole L).parent x) 0, show (whole L).embed 0 = 0 from (whole L).root.map_zero]

private lemma peak_exists (x : Site L) (hx : x ≠ 0) :
    (Finset.univ.filter (fun i => x i ≠ 0)).Nonempty := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hx
  exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩

private def peak (x : Site L) : Axis := if h : x ≠ 0 then
  (Finset.univ.filter (fun i => x i ≠ 0)).max' (peak_exists x h) else 0

private lemma lit (x : Site L) (hx : x ≠ 0) : x (peak x) ≠ 0 := by
  rw [peak, dif_pos hx]
  exact (Finset.mem_filter.mp (Finset.max'_mem _ (peak_exists x hx))).2

private lemma peak_ge (x : Site L) {i : Axis} (hi : x i ≠ 0) : i ≤ peak x := by
  have hx : x ≠ 0 := fun h => hi (congr_fun h _)
  rw [peak,dif_pos hx]
  exact Finset.le_max' (Finset.univ.filter (fun j => x j ≠ 0)) _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)

private lemma remote (x : Site L) {i : Axis} (h : peak x < i) : x i = 0 :=
  by_contra fun e => h.not_ge (peak_ge x e)

private lemma peak_le (x : Site L) (i : Axis) (h : ∀ j : Axis,i < j → x j=0) : peak x ≤ i := by
  rcases eq_or_ne x 0 with he|he
  · simp [peak,he]
  exact le_of_not_gt (fun hh => (lit x he) (h _ hh))

private def height (x : Site L) : ℕ := ∑ j, (x j).val

private lemma height_lower (x : Site L) {i : Axis} (hx : x i ≠ 0) : height (x-step i)<height x := by
  have hi : 0 < (x i).val := Nat.pos_of_ne_zero fun h => hx (by conv_lhs => rw [← ZMod.natCast_zmod_val (x i),h]; norm_num)
  have ht : 1<L.val := lt_of_le_of_lt hi (x i).val_lt
  have hh : (((x-step i : Site L) i).val)<(x i).val := by
    have hv : (1 : Per L).val=1 := ZMod.val_one'' ht.ne'
    simp only [Pi.sub_apply,step_apply,↓reduceIte]
    rw [ZMod.val_sub (hv ▸ hi),hv]; omega
  unfold height
  apply Finset.sum_lt_sum _ ⟨i,Finset.mem_univ _,hh⟩
  intro j _; rcases eq_or_ne j i with h|h
  · subst j; exact hh.le
  simp [h]

/-- The global axial tree viewed as a single-root forest. -/
def axle (L : Side) : Forest (whole L) where
  height := height
  bound x := calc
    _ ≤ ∑ _ : Axis, L.val := Finset.sum_le_sum fun i _ => (x i).val_lt.le
    _ = 4*(whole L).count.val := by simp [Axis,whole]
  up x := negDir (peak x)
  rise x hx := by
    rw [Step.vec_neg,← sub_eq_add_neg]
    exact height_lower _ (lit _ ((node x).mp hx))
  stays _ _ := by
    haveI : Subsingleton (Site (1:Side)) := inferInstanceAs (Subsingleton (Axis → ZMod 1))
    exact Subsingleton.elim ..

lemma trunk_here (x : Site L) (i : Axis) :
    (x,i)∈(axle L).trunks ↔ (x+step i : Site L) i≠0 ∧ ∀ j : Axis,i<j → x j=0 := by
  rw [(axle L).trunk_mem_iff]
  constructor
  · rintro ⟨y,hy,h⟩
    change (y-step (peak y),peak y)=(x,i) at h
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
    rw [sub_add_cancel]
    exact ⟨lit _ ((node y).mp hy),fun j hj => by simp [remote y hj,hj.ne']⟩
  rintro ⟨H,h⟩
  let z : Site L := x+step i
  have he : peak z=i := le_antisymm (peak_le z i fun j hj => by simp [z,hj.ne',h j hj]) (peak_ge z H)
  refine ⟨z,(node z).mpr (fun ht => H (congr_fun ht i)),?_⟩
  change (z-step (peak z),peak z)=(x,i); simp [he,z]

lemma trunk_count (L : Side) : (axle L).trunks.card=Fintype.card (Site L)-1 := by
  rw [Forest.trunks, Finset.card_image_of_injective]
  · rw [show Finset.univ.filter (leaf (whole L)) = Finset.univ.erase 0 by ext x; simp [node]]
    simp
  intro x y h
  change (x-step (peak x : Axis),peak x)=(y-step (peak y : Axis),peak y) at h
  rw [(Prod.mk.inj h).2] at h
  exact sub_left_inj.mp (Prod.mk.inj h).1

lemma free_count (L : Side) : Fintype.card (axle L).Free=3*Fintype.card (Site L)+1 := by
  rw [show Fintype.card (axle L).Free=Fintype.card (Edge (Site L))-Fintype.card (↥(axle L).trunks) by
    exact Fintype.card_subtype_compl _, Fintype.card_coe, trunk_count]
  rw [show Fintype.card (Edge (Site L)) = Fintype.card (Site L)*4 by simp [Edge,Axis]]
  have h : 0<Fintype.card (Site L) := Fintype.card_pos; omega

/-- One wrap per axis retained. -/
def handle (L : Side) (i : Axis) : Edge (Site L) := (-step i,i)

def handles (L : Side) := Finset.univ.image (handle L)

lemma no_handle (L : Side) (i : Axis) : handle L i ∉ (axle L).trunks := by
  unfold handle
  rw [trunk_here]; simp

/-- The links that will be paid by plaquette integration. -/
def swept (L : Side) : Finset (Edge (Site L)) := (Finset.univ \ (axle L).trunks) \ (handles L)

lemma swept_count (L : Side) : (swept L).card=3*Fintype.card (Site L)-3 := by
  have h : (handles L).card=4 := by
    rw [handles, Finset.card_image_of_injective]
    · simp [Axis]
    intro _ _ hh; exact congr_arg Prod.snd hh
  have hp : handles L ⊆ Finset.univ \ (axle L).trunks := fun i hi => by
    obtain ⟨j,-,rfl⟩ := Finset.mem_image.mp hi
    simp [no_handle]
  rw [swept, Finset.card_sdiff_of_subset hp, Finset.card_sdiff_of_subset (Finset.subset_univ _), trunk_count,h,Finset.card_univ]
  rw [show Fintype.card (Edge (Site L)) = Fintype.card (Site L)*4 by simp [Edge,Axis]]
  have hv : 0<Fintype.card (Site L) := Fintype.card_pos
  omega


def tier (e : Edge (Site L)) : Axis := max e.2 (peak e.1)

def priorityAt (e : Edge (Site L)) : Axis ×ₗ (ℕ ×ₗ ℕ) :=
  toLex (tier e,toLex (if e.2 < tier e then 0 else 1,height e.1))

/-- Positive edges read by this plaquette. -/
def edges (p : Face (Per L)) : Finset (Edge (Site L)) :=
  let i := p.2.val.1
  let j := p.2.val.2
  {(p.1,i),(p.1+step i,j),(p.1+step j,i),(p.1,j)}

lemma reads_four (x : Site L) (i j : Axis) (h : i < j) (e : Edge (Site L)) : e∈edges (x,⟨(i,j),h⟩) ↔
    e=(x,i) ∨ e=(x+step i,j) ∨ e=(x+step j,i) ∨ e=(x,j) := by simp only [edges,Finset.mem_insert,Finset.mem_singleton]

lemma exists_face (e : Edge (Site L)) (h : e∈swept L) :
    ∃ p : Face (Per L), e ∈ edges p ∧
      ∀ z∈edges p, z ≠ e → z∉(axle L).trunks → priorityAt z < priorityAt e := by
  obtain ⟨x,i⟩ := e
  let T := tier (x,i)
  have he : (x,i)∉(axle L).trunks := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h).1).2
  rcases lt_or_eq_of_le (show i ≤ T from le_max_left ..) with hi|hh
  ·
    let y : Site L := x-step T
    have hp : peak x = T := by
      change _ = max i (peak x); change i < max i (peak x) at hi
      rcases le_total i (peak x) with h|h
      · rw [max_eq_right h]
      rw [max_eq_left h] at hi; exact (lt_irrefl i hi).elim
    have hv : x ≠ 0 := fun H => by
      have ht : T = 0 := hp.symm.trans (by rw [H]; simp [peak])
      simp [ht] at hi
    have hx : x T≠0 := hp ▸ lit x hv
    have above (j : Axis) (hj : T<j) : x j=0 := remote x (hp ▸ hj)
    have hd (j : Axis) (hj : T<j) : y j = 0 := by simp [y,hj.ne',above j hj]
    have hy : y+step T=x := sub_add_cancel ..
    refine ⟨(y,⟨(i,T),hi⟩), (reads_four ..).mpr (Or.inr <| Or.inr <| Or.inl <| by rw [hy]), ?_⟩
    intro z hz h₁ h₂
    rcases (reads_four ..).mp hz with h|h|h|h <;> subst z
    · rcases lt_or_eq_of_le (show tier (y,i)≤T from max_le hi.le (peak_le y T hd)) with hw|hw
      · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hw)
      apply Prod.Lex.toLex_lt_toLex.mpr; right; refine ⟨hw,?_⟩
      change toLex (if i<tier (y,i) then 0 else 1,height y) < toLex (if i<T then 0 else 1,height x)
      rw [hw, if_pos hi]; exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl,height_lower x hx⟩)
    · exfalso; apply h₂; apply (trunk_here ..).2; constructor
      · rw [add_right_comm,hy]; simpa [hi.ne'] using hx
      intro j hj; simp [hd j hj,(hi.trans hj).ne']
    · simp [hy] at h₁
    · exfalso; apply h₂; exact (trunk_here ..).2 ⟨by rw [hy]; exact hx,hd⟩
  -- wrap
  let w : Site L := x+step i
  have above (j : Axis) (hj : i<j) : x j=0 := remote x ((le_trans (le_max_right ..) hh.symm.le).trans_lt hj)
  have hw : w i=0 := not_not.mp (fun H => he ((trunk_here x i).2 ⟨H,above⟩))
  have hu : w≠0 := by
    intro H
    have ha : x=-step i := eq_neg_of_add_eq_zero_left H
    apply (Finset.mem_sdiff.mp h).2
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,show handle L i=(x,i) by rw [ha]; rfl⟩
  let j := peak w
  have hd : w j≠0 := lit w hu
  have hj : j < i := lt_of_not_ge (fun hg => by
    rcases eq_or_lt_of_le hg with g|g
    · exact hd (by rw [← g]; exact hw)
    exact hd (by simp [w,above _ g,g.ne']))
  let y : Site L := x-step j
  have hy : y+step j=x := sub_add_cancel ..
  have hv (a : Axis) (h : i<a) : y a=0 := by simp [y,(hj.trans h).ne',above a h]
  refine ⟨(y,⟨(j,i),hj⟩), (reads_four ..).mpr (Or.inr <| Or.inl <| by rw [hy]),?_⟩
  intro z hz h₁ h₂
  rcases (reads_four ..).mp hz with a|a|a|a <;> subst z
  · rcases lt_or_eq_of_le (show tier (y,j) ≤ i from max_le hj.le (peak_le y i hv)) with hl|hl
    · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (lt_of_lt_of_le hl hh.le))
    apply Prod.Lex.toLex_lt_toLex.mpr; right
    refine ⟨hl.trans hh,?_⟩
    change toLex (if j<tier (y,j) then 0 else 1,height _) < toLex (if i<T then 0 else 1,height _)
    rw [hl,← hh, if_neg (lt_irrefl _), if_pos hj]
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl Nat.zero_lt_one)
  · simp [hy] at h₁
  · exfalso; apply h₂; apply (trunk_here ..).2; constructor
    · rw [add_right_comm,hy]; exact hd
    intro a ha
    rw [show y+step i=w-step j by dsimp [y,w]; abel]
    simp [ha.ne',remote w ha]
  · apply Prod.Lex.toLex_lt_toLex.mpr; right
    have ha : tier (y,i)=i := le_antisymm (max_le le_rfl (peak_le y i hv)) (le_max_left ..)
    refine ⟨ha.trans hh,?_⟩
    change toLex (if i<tier (y,i) then 0 else 1,height _) < toLex (if i<T then 0 else 1,height _)
    rw [ha,← hh]
    have hg : x j≠0 := by simpa [w,hj.ne] using hd
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl,height_lower x hg⟩)

/-- Chosen only on the swept edges. -/
def charged (e : ↥(swept L)) : Face (Per L) := Classical.choose (exists_face _ e.property)

lemma pays_here (e : ↥(swept L)) : e.val∈edges (charged e) := (Classical.choose_spec (exists_face _ e.property)).1
lemma pays_first (e f : ↥(swept L)) (h : e.val ∈ edges (charged f)) (he : e≠f) :
    priorityAt e.val < priorityAt f.val :=
  (Classical.choose_spec (exists_face _ f.property)).2 _ h (Subtype.coe_injective.ne he)
    ((Finset.mem_sdiff.mp (Finset.mem_sdiff.mp e.property).1).2)

lemma charged_injective (L : Side) : Injective (charged (L:=L)) := by
  intro e f h; by_contra hn
  exact (pays_first e f (h ▸ pays_here e) hn).not_gt (pays_first f e (h.symm ▸ pays_here f) (Ne.symm hn))


section integral

open Wilson MeasureTheory Filter
open scoped Topology Matrix.Norms.Frobenius

variable {G : Gauge}

lemma value_eq (U : Config G L) (x : Site L) {i j : Axis} (h : i<j) :
    faceValue U (x,⟨(i,j),h⟩) = U (x,i)*U (x+step i,j)*(U (x+step j,i))⁻¹*(U (x,j))⁻¹ := by
  simp [faceValue, square, travel, mul_assoc, add_right_comm x (step i) (step j)]

private lemma face_omit (U : Config G L) (a : Face (Per L)) {e} (he : e∉edges a) (v : G.El) :
    faceValue (Function.update U e v) a=faceValue U a := by
  obtain ⟨x,⟨i,j⟩,h⟩ := a
  rw [reads_four, not_or, not_or, not_or] at he
  rw [value_eq, value_eq]
  simp only [Function.update_of_ne (Ne.symm he.1), Function.update_of_ne (Ne.symm he.2.1),
    Function.update_of_ne (Ne.symm he.2.2.1), Function.update_of_ne (Ne.symm he.2.2.2)]

private lemma step_not_zero (h : 1<L.val) (x : Site L) (i : Axis) : x+step i≠x := by
  intro H
  have h' := congr_arg (fun p : Site L => p i) H
  change (x+step i : Site L) i=x i at h'; simp only [Pi.add_apply,step_apply,↓reduceIte] at h'
  have he : (1:Per L) = 0 := add_left_cancel (h'.trans (add_zero (x i)).symm)
  have hv := ZMod.val_one'' h.ne'
  rw [he,ZMod.val_zero] at hv; omega

lemma independent (h : 1<L.val) (U : Config G L) (a : Face (Per L)) (e) (he : e∈edges a) :
    MeasurePreserving (fun v => faceValue (Function.update U e v) a) G.probHaar G.probHaar := by
  obtain ⟨x,⟨i,j⟩,hi⟩ := a
  change i<j at hi
  let A : Edge (Site L) := (x,i)
  let B : Edge (Site L) := (x+step i,j)
  let C : Edge (Site L) := (x+step j,i)
  let D : Edge (Site L) := (x,j)
  simp_rw [value_eq]; change MeasurePreserving (fun v => Function.update U e v A * Function.update U e v B *
    (Function.update U e v C)⁻¹*(Function.update U e v D)⁻¹) G.probHaar G.probHaar
  have hB : A ≠ B := fun H => hi.ne (congr_arg Prod.snd H)
  have hC : A ≠ C := fun H => step_not_zero h x j (congr_arg Prod.fst H).symm
  have hD : A ≠ D := fun H => hi.ne (congr_arg Prod.snd H)
  have hi' : B ≠ C := fun H => hi.ne' (congr_arg Prod.snd H)
  have hx : B ≠ D := fun H => step_not_zero h x i (congr_arg Prod.fst H)
  have hy : C ≠ D := fun H => hi.ne (congr_arg Prod.snd H)
  rcases show e=A ∨ e=B ∨ e=C ∨ e=D from (reads_four ..).1 he with he|he|he|he
  · simp only [he,update_self,update_of_ne hB.symm,update_of_ne hC.symm,update_of_ne hD.symm]
    simpa only [mul_assoc,one_mul] using G.preserve_two_sided 1 (U B*(U C)⁻¹*(U D)⁻¹)
  · simp only [he,update_self,update_of_ne hB,update_of_ne hi'.symm,update_of_ne hx.symm]
    simpa only [mul_assoc] using G.preserve_two_sided (U A) ((U C)⁻¹*(U D)⁻¹)
  · simp only [he,update_self,update_of_ne hC,update_of_ne hi',update_of_ne hy.symm]
    exact (G.preserve_two_sided (U A * U B) (U D)⁻¹).comp G.preserve_inv
  simp only [he,update_self,update_of_ne hD,update_of_ne hx,update_of_ne hy]
  have h' := (G.preserve_two_sided (U A * U B * (U C)⁻¹) 1).comp G.preserve_inv
  simpa only [Function.comp_def,mul_one] using h'

private lemma by_mp {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} (F : B → ℝ) (hf : Integrable F ν) (t : A → B)
    (h : MeasurePreserving t μ ν) : (∫ x, F (t x)∂μ)=∫ y,F y∂ν := by
  have hx := integral_map (μ:=μ) (φ:=t) (f:=F) h.measurable.aemeasurable
    (by rw [h.map_eq]; exact hf.aestronglyMeasurable)
  rw [h.map_eq] at hx; exact hx.symm

/-- Single-link integration in the full Haar prior when the link is unused by q.
Proof averages a Haar translation in that one component. -/
lemma pull_link (h : 1<L.val) (p : Face (Per L)) (e : Edge (Site L)) (he : e∈edges p)
    (F : G.El → ℝ) (hf : Continuous F) (q : Config G L → ℝ) (hq : Continuous q)
    (hw : ∀ U : Config G L, ∀ u : G.El, q (Function.update U e u)=q U) :
    (∫ U, F (faceValue U p)*q U ∂prior G L)=(∫ x,F x∂G.probHaar)*(∫ U,q U∂prior G L) := by
  let T (t : G.El) (U : Config G L) := Function.update U e (t*U e)
  let f (U : Config G L) := F (faceValue U p)*q U
  have hT : Continuous (Function.uncurry T) := by
    apply continuous_pi; intro i
    rcases eq_or_ne i e with rfl|hi
    · simp only [Function.uncurry,T,update_self]; fun_prop
    simp only [Function.uncurry,T,update_of_ne hi]; fun_prop
  have hp : Continuous f := (hf.comp (continuous_travel _ _)).mul hq
  have h1 : Integrable f (prior G L) := hp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h2 : Integrable F G.probHaar := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have one (t : G.El) : (∫ U,f (T t U) ∂prior G L)=(∫ U,f U ∂prior G L) := by
    refine by_mp _ h1 _ ?_
    let v (i : Edge (Site L)) (u : G.El) := if i=e then t*u else u
    have hv (i : Edge (Site L)) : MeasurePreserving (v i) G.probHaar G.probHaar := by
      by_cases hh:i=e
      · simpa only [v,if_pos hh,mul_one] using G.preserve_two_sided t 1
      simpa only [v,if_neg hh] using! MeasurePreserving.id G.probHaar
    rw [show T t = fun U i => v i (U i) by funext U i; by_cases hh : i=e <;> simp [hh,T,v]]
    exact measurePreserving_pi _ _ hv
  let K := ∫ t,F t ∂G.probHaar
  have two (U : Config G L) : (∫ v,f (T v U)∂G.probHaar)= K*q U := by
    simp_rw [f, T, hw, integral_mul_const]; congr 1
    exact by_mp _ h2 _ ((independent h U p e he).comp (measurePreserving_mul_right G.probHaar (U e)))
  calc
    _ = ∫ v,∫ U,f (T v U) ∂prior G L ∂G.probHaar := by simp_rw [one]; simp [f]
    _ = ∫ U, ∫ v,f (T v U) ∂G.probHaar ∂prior G L := integral_integral_swap
          ((hp.comp hT).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    _ = _ := by simp_rw [two,integral_const_mul]; rfl

lemma charged_integral (h : 1<L.val) (F : G.El → ℝ) (hf : Continuous F) (s : Finset (↥(swept L))) :
    (∫ U : Config G L, (∏ i∈s,F (faceValue U (charged i))) ∂prior G L)=(∫ x,F x ∂G.probHaar)^s.card := by
  induction s using Finset.strongInductionOn
  rename_i s ih
  classical
  rcases Finset.eq_empty_or_nonempty s with rfl|hs
  · simp
  obtain ⟨i,hi,H⟩ := Finset.exists_max_image s (fun e => priorityAt e.val) hs
  have hw := ih _ (Finset.erase_ssubset hi)
  simp_rw [← Finset.mul_prod_erase s _ hi]
  rw [pull_link h (charged i) i.val (pays_here i) F hf (fun U => ∏ j∈s.erase i,F (faceValue U (charged j))) ?_ ?_, hw]
  · rw [← Finset.card_erase_add_one hi]
    rw [pow_succ']
  · refine continuous_finsetProd _ fun j _ => hf.comp (continuous_travel _ _)
  intro U u
  apply Finset.prod_congr rfl; intro x hx
  obtain ⟨hk,ho⟩ := Finset.mem_erase.mp hx
  refine congr_arg F (face_omit U _ ?_ u)
  exact fun ht => not_lt_of_ge (H _ ho) (pays_first i x ht hk.symm)

/-- Upper plaquette cost without dropping a boundary layer of wrap links. -/
theorem elimination (h : 1<L.val) (F : G.El → ℝ) (hf : Continuous F)
    (H : ∀ u, 0 ≤ F u) (K : ∀ u,F u ≤ 1) :
    (∫ U : Config G L, (∏ p : Face (Per L), F (faceValue U p))∂prior G L) ≤
      (∫ u,F u∂G.probHaar)^(3*Fintype.card (Site L)-3) := by
  classical
  let s := Finset.univ (α := ↥(swept L))
  let b := s.image charged
  rw [← swept_count, ← Fintype.card_coe, ← Finset.card_univ, ← charged_integral h F hf]
  refine integral_mono ?_ ?_ fun U => ?_
  · apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact continuous_finsetProd _ fun i _ => hf.comp (continuous_travel _ _)
  · apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact continuous_finsetProd _ fun i _ => hf.comp (continuous_travel _ _)
  calc
    _ ≤ ∏ x∈b,F (faceValue U x) := Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_univ _) (fun i _ => H _) (fun i _ _ => K _)
    _ = _ := Finset.prod_image (fun _ _ _ _ he => charged_injective L he)

end integral
end YM.Next.Rank.Axial
