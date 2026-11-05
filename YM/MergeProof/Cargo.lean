import YM.MergeProof.Decaf
import YM.MergeProof.Fruit
import YM.MergeProof.Garnish
import YM.MergeProof.Memo
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Menu
open Function Filter Lattice Wilson RG MeasureTheory Finset Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge Merge.Palette Accent Marker
open Extra.Multi GridApprox.Nil
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V ι β : Type}[DecidableEq V] {B:Census V} {G:Gauge}{f c:Side}{R:Rep G f}{E:Rep G c}
open Extra.Trajectories Planned.GuardedAtom
variable [Fintype V] {H:GaugeDoor R E}
    {w:V→ℝ} {F:V→ Config G f→ℂ} {K:V→Box f→ Config G f→ℂ} {P:V→ Box c→ Config G c→ℂ}{Q C:V→ℝ}{t:V→ℂ}{o:V→Site f}{p:V→Site c}
    {d A v e s:ℝ}{N:ℕ}
-- Tape at scaling v=1. Consumer separate powers; introduce e budget w. construct Garnish >=e+1 Attain.
lemma Booth (B:Census V)(h:∀ i,∃ x:Set Wing,x.Finite∧Tale x (o i) (p i) 1 (F i) (K i) (P i) (t i) (Q i) (C i) H){S:StepData c f}(hw:∀ i,0<w i)
    (hx:Tunes H)(hs:SoundDoor S H)(hp:Occupancy o N)(hd:0 ≤ d)(he:s+1 ≤ R.p.supportExponent)
    (hr:∀ i,2*w i*Q i ≤ d)(hA:∀ i,w i*C i ≤ A)(hc:e+1 ≤ E.p.supportExponent+2) :
    ∃ I:Type,∃ _:Fintype I,∃ m:I→Hat B R,Offer o m w R.p.B s (N*siteFactor R.p.B*d) ∧ ∃ ψ:V→Response G c,
      Garnish E.p p ψ w e A ∧ (∀ i U a,∑ j,owl (m j) H i a U=P i a U-hook E.activities E.p.threshold (ψ i) a U)∧
      (∀ U,∑ j,odour (m j) U=Mach B (fun i=> F i U-t i))∧∀ x U,∑ j,fragrance (m j) U x=Mach B (fun i=> K i x U):=by
   choose X hX I hI q t' ψ ht using h
   choose L hL M hM hQ hO hK hF using fun i=> narrow1 B i (ht i) (hX i) hs hx hw
   let Z := Σ i, L i; let f0 (i:Z):= M i.1 i.2
   have hT : Extra.Multi.Rooted (fun i=>(f0 i).s.val) (fun i=> (f0 i).M.crest) R.p.B R.p.supportExponent (fun i=> fare (f0 i) w) d:=by
      intro i; refine ⟨fun x=>?_, Summable.of_finite,?_⟩
      · dsimp only; split; exact mul_nonneg (Real.exp_pos _).le (Crew _ hw); rfl
      rw [tsum_fintype,Fintype.sum_sigma,sum_eq_single i];
      · calc
           _ = ∑ v, R.p.mass (M i v).M.crest (fare (M i v) w) := sum_congr rfl fun j _=> if_pos (show i∈(M i j).s.val from (hM i j).1.symm ▸ (show i∈(B.fire i).val from mem_singleton_self _))
           _ ≤ _ := (hQ i).trans (hr i)
      · intro j _ hj; apply Finset.sum_eq_zero; intro k _; exact if_neg fun hi=> hj (Finset.mem_singleton.mp (show i∈(B.fire j).val from (hM j k).1 ▸ (show i∈ (M j k).s.val from hi))|>.symm)
      simp
   have hG: Garnish E.p p ψ w e A:=by
      have he i:=(ht i).cost
      refine ⟨fun i t=> (he i).shaped _,fun i k=> (he i).marked _,fun i=>?_⟩; obtain ⟨v,hv,hQ⟩:= (he i).toll
      refine ⟨v,hQ,le_trans ?_ (hA i)⟩
      apply le_trans _ (mul_le_mul_of_nonneg_left (Extra.Multi.Budget.cap hv univ) (hw i).le); rw [Finset.mul_sum]; refine Finset.sum_le_sum fun j _=>?_ ; unfold reservedMass; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.exp_monotone (by gcongr)) (hQ j).1) (hw i).le
   refine ⟨Z,inferInstance,f0,⟨fun i=> ?_,root_hit (o:=o) hp (fun _=>Crew _ hw) hd ?_ (hT.mono (fun _=>Crew _ hw) (fun _=>le_rfl) he le_rfl)⟩,ψ,hG,fun i U a=>?_,fun U=>?_,fun x U=> ?_⟩
   · dsimp only [f0]; rw [(hM ..).1]; change Finset.image o ({i.1}:Finset V)⊆_; simp only [image_singleton,singleton_subset_iff]; exact (hM ..).2
   · rintro ⟨j,k⟩ _; exact ⟨j,(show j∈(M j k).s.val from (hM j k).1.symm ▸ (show j∈(B.fire j).val from mem_singleton_self _)),(hM j k).2⟩ -- show
   · rw [Fintype.sum_sigma,sum_eq_single i,hF];
     · intro b _ hb; apply Finset.sum_eq_zero; intro j _; apply if_neg; simp only [f0]; intro ht; exact hb ((B.fire_inj ..).mp (((hM ..).1).symm.trans ht)) -- eta
     simp
   · rw [Fintype.sum_sigma]; exact sum_congr rfl fun i _=> hO i U
   rw [Fintype.sum_sigma]; exact sum_congr rfl fun i _=> hK i x U
end YM.MergeProof.Menu
