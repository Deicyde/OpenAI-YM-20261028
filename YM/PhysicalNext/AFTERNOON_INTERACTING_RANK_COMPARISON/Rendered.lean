import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Dispenser
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Tableau

/-! # Rendering the density all step (fields and masks)

No interpolation or approximation change. Entire sum under common Λ; no
denominator, no field-integrated sectors skipped. Pass to the actual
interacting push at any query with auditFlags purchases before. Later use
unmarked restoration/log to make the Matric.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display
open Lattice Wilson Pressure RG Filter MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid SectorNext.Vacuum Precision
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {w x τ β : ℝ} {F : Lantern G S} {T : Tube G S}
    {P : Teller G} {J : ChartRatio G} {D : Allocation G S x w}
    {V : Config G c} {W ι : Type} [Fintype W] [DecidableEq W] {u : W → Site c} (Q : ι→ PaintCan S G x F.park u τ)

variable [Fintype ι]

def alex (A : Stores S) (V : Config G c) (i : Finset ι) := by
  exact enlist Q i ∧ cardGoal Q i=flags τ V ∧ A=stapled x (glow Q i) V

def achieved (Ω : Config G f → veil W) (Λ : Config G c → ℂ) (A : Stores S) (U : Config G c) :=
    ∀ k : Streak F.park,∀ z : RoomView A x k.wood G, spooled T F J D β Ω A k U z= Λ U • ∑ i∈univ.filter (alex Q A U),risen Q i A k U z

def earns_layout (T : Tube G S) := ∀ (i : Club Q) (V), validArea Q i V → ∀ k : Streak F.park, let A :=stapled x (glow Q i.val) V; Integrable (stage Q i.val A k V) (viewer T A x k.wood k.tag V)

noncomputable def solid (U : Config G c) (i : Finset (Club Q)) := (i:Set (Club Q)).PairwiseDisjoint (zone Q) ∧ cardGoal Q (draw Q i)=flags τ U

def tableau (T : Tube G S) (Λ : Config G c→ℂ) (U : Config G c) := Λ U • ∑ i∈univ.filter (solid Q U), ∏ s∈i,proceeds Q T s U

set_option maxHeartbeats 500000 in
/-- Enact AFTER local assembly. -/
theorem rendered {Ω : Config G f → veil W} {Λ} (hg : Envelope Ω) (h : GaugeInvariant Ω) (ht : Boosted T P x)
    (hy : Coupler T F J D β) (hm : ∀ A V,Positioned x A V → achieved Q (T:=T) (J:=J) (D:=D) (β:=β) Ω Λ A V) (he : earns_layout Q T) (V : Config G c) :
    S.push β Ω V=tableau Q T Λ V := by
  rw [arriving T F J D β ht.produced.branched _ hg h hy V]
  let H(A : Stores S):= univ.filter (alex Q A V)
  let v(i:Finset ι):= glance T (risen Q i) (glow Q i) V
  have hh A k i (hi:i∈H A): Integrable (risen Q i A k V) (viewer T A x k.wood k.tag V):= by
    obtain ⟨hh,hx,hA⟩:= (mem_filter.mp hi).2; subst A
    obtain ⟨s,H,hs⟩:= luminous Q i hh
    exact (projected_club Q ht i hh V hx s H hs (fun j hj=>he j V (zone_pass Q H (hs.symm ▸ hx) j hj))).1 k
  let p A k := ∫ z,spooled T F J D β Ω A k V z∂ viewer T A x k.wood k.tag V
  have hP A (hA : Positioned x A V): ∑ k,Streak.share k • p A k=Λ V • ∑ t∈H A, v t := by
    have ht k: p A k= Λ V • ∑ i∈H A, (∫ z,risen Q i A k V z ∂viewer T A x k.wood k.tag V):= by
      unfold p; simp_rw [hm A V hA k]; rw [integral_smul,integral_finsetSum _ (hh A k)]
    simp_rw [ht, smul_comm (Streak.share _) (Λ V),← Finset.smul_sum]; apply congr_arg (Λ V • ·)
    simp_rw [Finset.smul_sum]; rw [sum_comm]; apply sum_congr rfl; intro i hi
    have hl:A=stapled x (glow Q i) V:= (mem_filter.mp hi).2.2.2
    unfold v glance; rw [hl]
  have hv A: ¬Positioned x A V→ H A=∅:= by
    intro hm; refine eq_empty_iff_forall_notMem.mpr fun i hi=> ?_
    exact hm ((mem_filter.mp hi).2.2.2.symm ▸ position ..)
  -- evaluate outer as single filtered sum (tag-order unchanged)
  calc
    _ = Λ V • ∑ A,∑ t∈H A, v t := by
      rw [Finset.smul_sum]; apply sum_congr rfl; intro i hi; split_ifs with hc
      · exact hP i hc
      rw [hv _ hc,sum_empty,smul_zero]
    _ = _:= by
      unfold tableau; apply congr_arg (Λ V • ·)
      let W:= univ.filter (fun t : Finset ι=> enlist Q t∧cardGoal Q t=flags τ V)
      calc
        _ = ∑ t∈ W,v t := by
          unfold H; simp_rw [sum_filter]; unfold W; rw [sum_comm,sum_filter]; apply sum_congr rfl; intro t _
          split_ifs with hz
          · rw [Finset.sum_eq_single (stapled x (glow Q t) V), if_pos (show alex Q _ _ t from ⟨hz.1,hz.2,rfl⟩)]
            intro a _ ha; exact if_neg (fun hp=>ha hp.2.2)
            simp
          exact sum_eq_zero (fun i _=>if_neg (fun hh=>hz ⟨hh.1,hh.2.1⟩))
        _ = _:= by
          symm
          apply sum_bij (fun i _=>draw Q i) (fun i hi=> ?_) (fun i hi j hj h=>?_) (fun i hi=>?_) (fun i hi=>?_)
          · exact mem_filter.mpr ⟨mem_univ _,drew Q _ (mem_filter.mp hi).2.1,(mem_filter.mp hi).2.2⟩
          · have hp := Eq.trans (recovered Q (mem_filter.mp hi).2.1).symm (by rw [h, recovered Q (mem_filter.mp hj).2.1])
            exact Finset.image_injective Subtype.val_injective hp
          · obtain ⟨hh,hf⟩:= (mem_filter.mp hi).2
            obtain ⟨s,hs,hS⟩:= luminous Q i hh
            exact ⟨s,mem_filter.mpr ⟨mem_univ _,hs,hS.symm ▸ hf⟩,hS⟩
          obtain ⟨hh,hf⟩:= (mem_filter.mp hi).2
          exact (projected_club Q ht _ (drew Q i hh) V hf i hh rfl fun i hi=> he i V (zone_pass Q hh hf i hi)).2.symm
end YM.PhysicalNext.InteractingRank.Display
