import YM.Ac.Table
import YM.Next.MULTISOURCE.Couple
import YM.Next.MULTISOURCE.Measure
import YM.Next.MULTISOURCE.Monomial
import YM.Next.MULTISOURCE.Touch



/-!
# Read compressed *marked* packets
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Couples
open RG Wilson Lattice Finset Function Marker
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {n : Side} {V : Type} [DecidableEq V] [Fintype V] (Y : V → Support n) {G : Gauge}

-- Recipe for K marker in singleton terms at cutoff. Aggregated exactly on pack addresses.
def ballast (Y : Support n) (P : Rep G n) (C : Config G n → ℂ) (q : Pack n) (U : Config G n) :=
  if q.zone ∩ flags P.p.threshold U = q.flagsAt then C U *
    ∑ s ∈ univ.filter (fun s : Finset (Pack n) => s.Nonempty ∧ (s:Set (Pack n)).PairwiseDisjoint Pack.zone ∧
      (∀ j∈s,¬ Disjoint Y j.zone) ∧ Y ∪ s.biUnion Pack.zone=q.zone ∧ s.biUnion Pack.flagsAt=q.flagsAt),
      ∏ j∈s, incumbent P U j else 0

def trays (Y : V → Support n) (q : Pack n) := (boxes Y).filter fun a => fused Y a=q

def master (P : Rep G n) (C : V → Config G n → ℂ) (U : Config G n) : Atom n V → ℂ :=
    Sum.elim (incumbent P U) (fun i => C i U)

def track {R : Census V} (P : Rep G n) (C : V → Config G n → ℂ) (U : Config G n) : Atom n V → Poly R :=
    Sum.elim (fun i => Poly.send R.quiet (incumbent P U i)) (fun i => Poly.send (R.fire i) (C i U))

/-- Formula per particular collection of sources, NOT one coefficient per
configuration (and even singleton output retains the complete overlap). -/
def payload (P : Rep G n) (C : V → Config G n → ℂ) (T : Finset V) (q : Pack n) (U : Config G n) :=
    ∑ j ∈ trays Y q with j.toRight=T, earning Y (flags P.p.threshold U) (master P C U) j

lemma each_payload (P : Rep G n) (C : V → Config G n → ℂ) {R : Census V} (T : R.Mode)
    (q : Pack n) (U : Config G n) :
    (till Y (flags P.p.threshold U) (track P C U) q).part T = payload Y P C T.val q U := by
  let F := track (R:=R) P C U
  have he j : (earning Y (flags P.p.threshold U) F j).part T =
      if j.toRight=T.val then earning Y (flags P.p.threshold U) (master P C U) j else 0 := by
    unfold earning; split_ifs with h h' h'
    · rw [split_product j, show (∏ i∈ j.toLeft,F (Sum.inl i)) =
          Poly.bead R (∏ i∈j.toLeft, incumbent P U i) from (map_prod (Poly.bead R) ..).symm]
      rw [Poly.product_bead, Poly.part_smul]
      change _ * (∏ i ∈ j.toRight, Poly.send (R.fire i) (C i U)).part T=_
      rw [monomial, if_pos h'.symm, split_product j _]; rfl
    · rw [split_product j, show (∏ i∈ j.toLeft,F (Sum.inl i)) =
          Poly.bead R (∏ i∈j.toLeft, incumbent P U i) from (map_prod (Poly.bead R) ..).symm]
      rw [Poly.product_bead, Poly.part_smul]
      change _ * (∏ i ∈ j.toRight, Poly.send (R.fire i) (C i U)).part T=_
      rw [monomial, if_neg (Ne.symm h'), mul_zero]
    all_goals rfl
  unfold till; rw [Poly.part_sum]; unfold payload; conv_rhs => rw [Finset.sum_filter]
  refine sum_congr ?_ (fun i _ => he i)
  rfl

lemma empty_payload (P : Rep G n) (C : V → Config G n → ℂ)
    (q : Pack n) (U : Config G n) {δ κ : ℝ} (H : P.activities.Valid P.p δ κ) :
    payload Y P C ∅ q U=incumbent P U q := by
  let s : Recipe n V := {Sum.inl q}
  have he : s∈boxes Y := alone Y q
  have hf : fused Y s=q := fused_one ..
  have hr : ground Y s=q.zone := (hf ▸ merged_zone Y he).symm
  have ht : tags s=q.flagsAt := (hf ▸ merged_tags Y he).symm
  unfold payload; rw [sum_eq_single s]
  · rw [earning,hr,ht]; split <;> rename_i hi
    · rw [prod_singleton]; rfl
    by_contra h'; exact hi ((incumbent_legible P q H.forced).inventory U (Ne.symm h'))
  · intro b hb hh; obtain ⟨hb, h'⟩ := mem_filter.mp hb
    simp only [trays,mem_filter] at hb
    exact False.elim (hh (purchase Y hb.1 hb.2 h'))
  intro hj; refine False.elim (hj (mem_filter.mpr ⟨?_,?_⟩))
  · simp only [trays,mem_filter]; exact ⟨he,hf⟩
  ext; simp [s]

lemma till_eq (P : Rep G n) (C : V → Config G n → ℂ) (R : Census V)
    (q : Pack n) (U : Config G n) {δ κ : ℝ} (H : P.activities.Valid P.p δ κ) :
    till Y (flags P.p.threshold U) (track P C U) q = Poly.send R.quiet (incumbent P U q)+
      lit R fun i => payload Y P C i.sites q U := by
  ext i; rw [each_payload,Poly.part_plus]; by_cases h : i.val.Nonempty
  · rw [Poly.part_send, if_neg (show i ≠ R.quiet from fun e => not_nonempty_empty (e ▸ h)), zero_add]
    exact (part_lit (fun j => payload Y P C j.sites q U) (⟨i,h⟩ : Hot R)).symm
  rw [show i=R.quiet from Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp h),part_lit_quiet,add_zero,
    Poly.part_send,if_pos rfl]; exact empty_payload Y _ _ _ U H

omit [DecidableEq V] in
private lemma mark_host (j : Recipe n V) (q : Pack n) : j∈trays Y q ↔ j∈ boxes Y ∧
    ground Y j=q.zone ∧ tags j=q.flagsAt := by
  simp only [trays,mem_filter]; constructor
  · rintro ⟨h,hp⟩; exact ⟨h,(merged_zone Y h).symm.trans (congrArg Pack.zone hp),
      (merged_tags Y h).symm.trans (congrArg Pack.flagsAt hp)⟩
  rintro ⟨h,hp,H⟩; exact ⟨h,Subtype.ext ((fused_eq Y h).trans (Prod.ext hp H))⟩

lemma single_payload (P : Rep G n) (C : V → Config G n → ℂ) (q : Pack n) (i : V) (U : Config G n) :
    payload Y P C {i} q U = ballast (Y i) P (C i) q U := by
  unfold ballast payload; split_ifs with h
  · rw [Finset.mul_sum]
    symm
    refine Finset.sum_bij (fun a _ => Finset.disjSum a {i}) ?_ (fun a ha b hb H =>
      by simpa using congrArg Finset.toLeft H) ?_ ?_
    · intro a ha
      obtain ⟨ht,ha,hH,he,hq⟩ := (mem_filter.mp ha).2
      refine mem_filter.mpr ⟨(mark_host ..).mpr ⟨(plus_box Y i a).mpr ⟨ht,ha,hH⟩,
        (plus_span ..).trans he,?_⟩, toRight_disjSum⟩
      unfold tags; rw [toLeft_disjSum]; exact hq
    · intro b hb
      obtain ⟨hb,H⟩ := mem_filter.mp hb
      obtain ⟨hs,hb,hc⟩ := (mark_host ..).mp hb
      have he : b.toLeft.disjSum {i}=b := by rw [← H]; exact parts_word _
      obtain ⟨hq,hq',hr⟩ := (plus_box Y i b.toLeft).mp (by rwa [he])
      refine ⟨b.toLeft,mem_filter.mpr ⟨mem_univ _,hq,hq',hr,?_,hc⟩,he⟩
      rw [← plus_span,he,hb]
    intro a ha
    obtain ⟨hb,H⟩ := mem_filter.mp ha
    unfold earning; rw [if_pos (by rw [plus_span,H.2.2.2.1, tags,toLeft_disjSum,H.2.2.2.2]; exact h)]
    rw [prod_disjSum,prod_singleton,mul_comm]; rfl
  apply sum_eq_zero; intro a ha; obtain ⟨_,hb,hc⟩ := (mark_host ..).mp (mem_filter.mp ha).1
  unfold earning; rw [if_neg (by rw [hb,hc]; exact h)]
end YM.Multi.Couples
