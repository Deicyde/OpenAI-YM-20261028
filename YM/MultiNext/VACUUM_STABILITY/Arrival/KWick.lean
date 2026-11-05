import YM.MultiNext.VACUUM_STABILITY.Arrival.Pay

set_option warningAsError false

/-!
# At input vacuum pack alphabet. Include labelled insertions or keep
per-Pack totals and obtain the row identities. Same histories for all z.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Arrival.Flock
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp Restock
open Jets Hits Puff
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {V : Type} {n : Side} (F : Flock V G n) (Q : Rep G n)

abbrev Cases (F : Flock V G n) : Type := ℕ ⊕ Augment F

def owes : Cases F → Pack n := Sum.elim (Pack.ofAddress Q.activities) (hardZone F)

def scrip : Cases F → Stamp V (Config G n) := Sum.elim (fun i => ⟨0, fun U => (Q.activities.K i U:ℂ)⟩) (addition F)

def sits (U : Config G n) (s : Finset (Cases F)) := s.image (owes F Q) ∈ Pack.clears (flags Q.p.threshold U) ∧ Set.InjOn (owes F Q) s

variable [Fintype V] (z : V→ℂ)

def attends (s : Finset (Cases F)) (U : Config G n) := if sits F Q U s then ∏ i∈s,(scrip F Q i).tell z U else 0

namespace Attended
variable {F} {o : V → Site n} {k : V → ℝ} {κ : ℝ} {D : V → Pulse G n} (h : Attended F Q.p D o k κ)
variable {σ c Λ δ b η : ℝ} (H : Q.Lawful σ c Λ δ b)

include h H
omit [Fintype V] in
lemma inspected (i : Cases F) : Legible Q.p (owes F Q i) (scrip F Q i).ink := by
  obtain i|i:=i
  · have he := H.labels.forced
    refine ⟨Complex.continuous_ofReal.measurable.comp (he.meas i), fun k U => congrArg Complex.ofReal (he.sym i k U),
      fun U V hx hy => congrArg Complex.ofReal (he.reads i U V hx hy),fun U hu => (he.permit _ _ ?_).1⟩
    intro hh; apply hu; change (Q.activities.K i U:ℂ)=_; rw [hh,Complex.ofReal_zero]
  exact ((h.authorizations _).bears _).1
omit h H

include h H in
lemma hard_budget (z : V→ℂ) (hz : z∈allot o k η) (hκ : 0 < κ) :
    ∃ (X : Cases F → ℝ) (v : Cases F→Site n), (∀ i, v i∈(owes F Q i).zone ∧ 0 ≤ X i ∧ ∀ U, ‖(scrip F Q i).tell z U‖ ≤ X i) ∧
    Locations Q.p (fun i => (owes F Q i).zone) v X (b+κ*η) ∧
      (∀ i : Augment F,v (.inr i)=o i.val.1 ∧ X (.inr i)=stipendK F z i) := by
  obtain ⟨g,hg,hG⟩:=H.labels.boundK
  obtain ⟨hf,hF⟩:= h.issued_hard z hz hκ.le
  choose x hx using fun i : ℕ => (Q.activities.forced i).inventory_ne
  have hs (i : ℕ) : x i∈ (owes F Q (.inl i)).zone := (Q.activities.forced i).inventory_sup (hx i)
  let v := Sum.elim x fun i : Augment F => o i.val.1
  let X := Sum.elim g (stipendK F z)
  refine ⟨X,v,?_,fun i => ?_,fun _ => ⟨rfl,rfl⟩⟩
  · rintro (i|i)
    · refine ⟨hs i,(hg i).1, fun U => ?_⟩; simp only [scrip,Sum.elim_inl,Stamp.tells,Stamp.beat_zero,one_mul,Complex.norm_real]; exact (hg _).2 _
    exact ⟨(hF _).1,(hF _).2.2⟩
  apply Absolute.union _ (hf _); apply Absolute.compare (hG i)
  · intro j; dsimp only [owes,Function.comp_apply,v,X,Sum.elim_inl]; split; exact mul_nonneg (Real.exp_pos _).le (hg _).1; exact le_rfl
  intro j; dsimp only [Function.comp_apply,owes,v,X,Sum.elim_inl]; split
  · rename_i he; rw [if_pos (show i ∈ _ from he ▸ hs j)]; exact le_rfl
  exact (hG _).1 _

include h H in
lemma partner (s : Finset (Cases F)) (z : V → ℂ) : Measurable (attends F Q z s) ∧ GaugeInvariant (attends F Q z s) := by
  have he i := (inspected Q h H i).scale (Stamp.beat (scrip F Q i).name z)
  unfold attends; constructor
  · apply Measurable.ite _ (Finset.measurable_fun_prod _ fun i _ => (he i).borel) measurable_const
    by_cases hx : Set.InjOn (owes F Q) s
    · simp only [sits,hx,and_true]; exact Pack.neighborhood ..
    simp [sits,hx]
  intro k U
  have ht : sits F Q (Lattice.gauge k U) s ↔ sits F Q U s := by simp [sits]
  exact if_ctx_congr ht (fun _ => prod_congr rfl fun i _ => (he i).symmetry k U) fun _ => rfl

include h H in
lemma usingK (z : V→ℂ) {U : Config G n} (q : Pack n) : ∑' i : Cases F, (if owes F Q i=q then (scrip F Q i).tell z U else 0) =
    incumbent Q U q+∑ i,z i*(D i).2 q U := by
  let f (i : Cases F) := if owes F Q i=q then (scrip F Q i).tell z U else 0
  let s (i : ℕ) := (Q.activities.K i U:ℂ)
  have he i : f (.inl i)= (if Pack.ofAddress Q.activities i=q then s i else 0) := by dsimp only [f,owes,s,scrip,Sum.elim_inl]; simp
  have ht : Summable (f ∘ Sum.inl) := by
    have hh : Summable s := by
      obtain ⟨c,hc,hC⟩:=Activities.K_total H.labels.boundK
      exact (hc.of_nonneg_of_le (fun i => norm_nonneg (s i)) fun i => by unfold s; rw [Complex.norm_real]; exact (hC _).2 _).of_norm
    exact (sift hh (fun i => Pack.ofAddress Q.activities i=q)).congr fun i => (he i).symm
  rw [Absolute.union_tsum (f:=f) ht (hasSum_fintype _).summable]
  congr 1
  · unfold incumbent Pack.collect; apply tsum_congr; intro i; rw [he]
  let k (i : V × Pack n) := if i.2=q then z i.1*(F i.1).d i.2 U else 0
  have hk : ∑' i : Augment F, k i.val = ∑' i,k i := by
    refine tsum_subtype_eq_of_support_subset ?_
    intro i hi; change k i ≠ 0 at hi; change _ ≠ 0; intro h; apply hi; unfold k; split
    · rw [h]; simp
    rfl
  have hv (i : Augment F) : f (.inr i)=k i.val := by
    unfold f k owes scrip; simp_rw [Sum.elim_inr, addition, Stamp.tells, Stamp.beat_spike]; rfl
  change ∑' i,f (.inr i) = _
  rw [tsum_congr hv,hk,tsum_fintype,Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro i _
  unfold k; simp; exact Or.inl (congrArg (fun u : Pulse G n => u.2 q U) (h.fact i))

include h H in
lemma runs (z : V→ℂ) (hz : z∈allot o k η) (hκ : 0 < κ) (U : Config G n) :
    (∑' s,attends F Q z s U) = ∑ i∈ Pack.clears (flags Q.p.threshold U), ∏ j∈i, (incumbent Q U j+∑ i,z i*(D i).2 j U) := by
  obtain ⟨f,x,hx,hf,-⟩:=hard_budget Q h H z hz hκ
  let t i := (scrip F Q i).tell z U
  have he : Summable fun i => ‖t i‖ := (hf.imposed fun i => (hx i).2.1).of_nonneg_of_le (fun i => norm_nonneg _) fun i => (hx i).2.2 _
  let L := Pack.clears (flags Q.p.threshold U)
  have hp := Alternatives.classify (owes F Q) he (fun i => i∈L)
  rw [tsum_fintype] at hp
  have hu i : incumbent Q U i+∑ j,z j*(D j).2 i U = ∑' j, if owes F Q j=i then t j else 0 := (h.usingK Q H z i).symm
  simp_rw [hu]; refine Eq.trans ?_ (hp.symm.trans ?_)
  · refine tsum_congr fun i => ?_; unfold attends; split
    · rename_i h; obtain ⟨H,hg⟩:=h; rw [if_pos ⟨H,hg⟩]
    rename_i h; split; rename_i H; exact False.elim (h H); rfl
  have ht := Finset.sum_ite_mem Finset.univ L (fun i => ∏ j∈i, ∑' l, if owes F Q l=j then t l else 0)
  rw [Finset.univ_inter] at ht; exact ht
end Attended
end YM.Multi.Vacuum.Arrival.Flock
