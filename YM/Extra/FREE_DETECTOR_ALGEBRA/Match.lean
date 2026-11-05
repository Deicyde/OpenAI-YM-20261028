import YM.Extra.FREE_DETECTOR_ALGEBRA.Occurrences

set_option warningAsError false

/-! Remove the distinguished pair in a matching; precisely compare both
sums. Off coincidences where entry symmetry holds. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD.Pair
open Function Filter Set Maxwell Wick Wick.Occ
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {n : ℕ} {W Y : Powers G n}

theorem match_equal {P Q : Matching W} (he : ∀ v, partner P v = partner Q v) : P=Q := Subtype.ext (Equiv.ext he)

private theorem mkPair (p : Occ W → Occ W) (hp : Involutive p) (hh : ∀ v, (p v).label≠v.label) :
    ∃ Q : Matching W, ∀ v, partner Q v=p v := by
  let w := Equiv.ofBijective p hp.bijective
  have he : w * w = (1: Equiv.Perm (Occ W)) := Equiv.ext (fun v => hp v)
  exact ⟨⟨w,he,hh⟩,fun v => rfl⟩

namespace Edge
variable {f : Occ W → Occ Y} {p q : Occ Y} (h : Edge f p q)
include h

lemma ne : p ≠ q := fun he => h.apart (congr_arg label he)

lemma cases (v : Occ Y) : v=p ∨ v=q ∨ ∃ w, v=f w := by
  by_cases he : v=p; exact Or.inl he
  by_cases ht : v=q; exact Or.inr (Or.inl ht)
  obtain ⟨w,hw⟩ := h.fill _ he ht; exact Or.inr (Or.inr ⟨w,hw.symm⟩)

lemma forward (P : Matching W) :
    ∃ Q : Matching Y, partner Q p=q ∧ ∀ v, f (partner P v)=partner Q (f v) := by
  classical
  have he (v : Occ Y) : ∃ y : Occ Y, (v=p→ y=q) ∧ (v=q→ y=p) ∧ (∀ w, v=f w → y=f (partner P w)) := by
    rcases h.cases v with rfl | rfl | ⟨w,rfl⟩
    · exact ⟨q,fun _ => rfl,fun ht => (h.ne ht).elim,fun w ht => (h.not_left w ht.symm).elim⟩
    · exact ⟨p,fun ht => (h.ne ht.symm).elim,fun _ => rfl,fun w ht => (h.not_right w ht.symm).elim⟩
    exact ⟨f (partner P w),fun ht => (h.not_left _ ht).elim,fun ht => (h.not_right _ ht).elim,
      fun b ht => by rw [h.good ht]⟩
  choose r hr hs ht using he
  have hi : Involutive r := by
    intro v
    rcases h.cases v with h|h|⟨w,rfl⟩
    · subst v; rw [hr _ rfl,hs _ rfl]
    · subst v; rw [hs _ rfl,hr _ rfl]
    rw [ht _ w rfl,ht _ (partner P w) rfl,turn]
  have hw (v) : (r v).label≠v.label := by
    rcases h.cases v with he|he|⟨w,rfl⟩
    · subst v; rw [hr _ rfl]; exact Ne.symm h.apart
    · subst v; rw [hs _ rfl]; exact h.apart
    rw [ht _ w rfl,h.name,h.name]; exact different P w
  obtain ⟨Q,hQ⟩ := mkPair r hi hw
  exact ⟨Q,(hQ _).trans (hr p rfl), fun v => ((hQ _).trans (ht _ v rfl)).symm⟩

lemma backward (Q : Matching Y) (hp : partner Q p=q) :
    ∃ P : Matching W, ∀ v, f (partner P v)=partner Q (f v) := by
  have he (v : Occ W) : ∃ w, f w=partner Q (f v) := by
    refine h.fill (partner Q (f v)) (fun ht => h.not_right v ?_) fun ht => h.not_left v ?_
    · exact (turn Q _).symm.trans ((congr_arg (partner Q) ht).trans hp)
    exact (partner Q).injective (ht.trans hp.symm)
  choose r hr using he
  have hi : Involutive r := fun v => h.good (by rw [hr,hr,turn])
  have hh (v) : (r v).label≠v.label := by rw [← h.name,hr, ← h.name v]; exact different Q (f v)
  obtain ⟨P,hP⟩ := mkPair r hi hh
  exact ⟨P,fun v => by rw [hP,hr]⟩

lemma unique {P : Matching W} {Q L : Matching Y} (hq : partner Q p=q) (hl : partner L p=q)
    (hr : ∀ v, f (partner P v)=partner Q (f v)) (hs : ∀ v, f (partner P v)=partner L (f v)) : Q=L := by
  apply match_equal; intro v
  rcases h.cases v with he|he|⟨w,rfl⟩
  · subst v; rw [hq,hl]
  · subst v
    exact ((congr_arg (partner Q) hq).symm.trans (turn Q _)).trans (((congr_arg (partner L) hl).symm.trans (turn L _)).symm)
  rw [← hr,← hs]

/-- Exact fiber equivalence. -/
lemma match_fiber : ∃ L : Matching W ≃ {Q : Matching Y // partner Q p = q},
    ∀ Q v, f (partner Q v)=partner (L Q).val (f v) := by
  classical
  choose r hr hs using h.forward
  let b (P : Matching W) : {Q : Matching Y // partner Q p=q} := ⟨r P,hr P⟩
  have hi : Injective b := by
    intro P T ht
    have hh : r P = r T := congr_arg Subtype.val ht
    exact match_equal fun v => h.good (by rw [hs,hs,hh])
  have he : Surjective b := by
    rintro ⟨Q,hq⟩; obtain ⟨P,hP⟩ := h.backward Q hq
    exact ⟨P,Subtype.ext (h.unique (hr P) hq (hs P) hP)⟩
  exact ⟨Equiv.ofBijective _ ⟨hi,he⟩,hs⟩

private lemma pair_lt (P : Matching W) (Q : Matching Y) (hq : partner Q p=q)
    (hr : ∀ v, f (partner P v)=partner Q (f v)) (hs : p.label<q.label) (x : Points n) :
    Occ.graph x Q = edge x p q * Occ.graph x P := by
  have he (v : Occ W) : f v ∈ corners Q ↔ v ∈ corners P := by simp [corners,← hr,h.name]
  have ht : corners Q = insert p ((corners P).image f) := by
    ext v; rcases h.cases v with h1|h1|⟨w,rfl⟩
    · subst v; simp [corners,hq,hs]
    · subst v
      have hb : partner Q q=p := (congr_arg (partner Q) hq).symm.trans (turn Q _)
      have hi : q ∉ Finset.image f (corners P) := by simp only [Finset.mem_image]; exact not_exists.mpr fun v ⟨_,hv⟩ => h.not_right _ hv
      simp only [Finset.mem_insert, Ne.symm h.ne,hi,or_self]
      simp [corners,hb,hs.not_gt]
    rw [he w]
    simp only [Finset.mem_insert,h.not_left w,false_or, Finset.mem_image]
    exact ⟨fun hw => ⟨w,hw,rfl⟩,fun ⟨a,ha,he⟩ => h.good he ▸ ha⟩
  unfold Occ.graph; rw [ht, Finset.prod_insert, hq,Finset.prod_image h.good.injOn]
  · congr 1
    exact Finset.prod_congr rfl fun v _ => by rw [← hr]; simp [edge,h.name,h.read]
  exact fun hm => Exists.elim (Finset.mem_image.mp hm) fun w ⟨_,hw⟩ => h.not_left _ hw

lemma graph_link (P : Matching W) (Q : Matching Y) (hq : partner Q p=q)
    (hr : ∀ v, f (partner P v)=partner Q (f v)) {x : Points n} (hx : x ∈ conf n) :
    Occ.graph x Q = edge x p q * Occ.graph x P := by
  rcases lt_or_gt_of_ne h.apart with he|he
  · exact h.pair_lt P Q hq hr he x
  have hl : Edge f q p := ⟨h.good,h.name,h.read,h.not_right,h.not_left,h.apart.symm,fun v hv hw => h.fill v hw hv⟩
  rw [hl.pair_lt P Q ((congr_arg (partner Q) hq).symm.trans (turn Q _)) hr he]
  congr 1
  exact entry_symmetric _ _ ((show Injective x.ofLp from hx).ne hl.apart)

lemma fiber_coeff {x : Points n} (hx : x ∈ conf n) :
    ∑ Q : {Q : Matching Y // partner Q p=q}, Occ.graph x Q.val = edge x p q * monomial x W := by
  obtain ⟨L,hL⟩ := h.match_fiber
  unfold monomial; rw [Finset.mul_sum]
  exact (Fintype.sum_equiv L _ _ fun P => (h.graph_link P _ (L P).property (hL P) hx).symm).symm
end Edge

lemma mon_bump (W : Powers G n) (i : Fin n) (a : Slot G) {x : Points n} (hx : x ∈ conf n) :
    monomial x (bump W i a) = ∑ q : {p : Occ W // p.label≠i}, entry a q.val.probe (x i) (x q.val.label) *
      monomial x (smaller W q.val.label q.val.probe) := by
  let Y := bump W i a
  let f := earlier W i a
  let p := added W i a
  let S := {p : Occ W // p.label≠i}
  have he (Q : Matching Y) : ∃ q : S, f q.val = partner Q p := by
    have ht := hole W i a
    obtain ⟨v,hv⟩ := ht.fill _ (show partner Q p≠p from fun he => different Q p (congr_arg label he))
    exact ⟨⟨v,by rw [← ht.name v,hv]; exact different Q p⟩,hv⟩
  choose b hb using he
  unfold monomial; rw [← Fintype.sum_fiberwise b (fun Q => Occ.graph x Q)]
  apply Finset.sum_congr rfl
  intro q _
  have H := q.property
  obtain ⟨r,hr⟩ := with_edge W i a q.val q.property
  have he (Q : Matching Y) : b Q=q ↔ partner Q p=f q.val := by rw [← hb]; exact ⟨fun he => he ▸ rfl,fun he => Subtype.ext ((hole ..).good he)⟩
  let L : {Q : Matching Y // b Q=q} ≃ {Q : Matching Y // partner Q p=f q.val} := Equiv.subtypeEquivRight he
  refine Eq.trans (Fintype.sum_equiv L (fun P => Occ.graph x P.val) (fun P => Occ.graph x P.val) fun P => rfl) ?_
  exact hr.fiber_coeff hx
end YM.Extra.FD.Pair
