import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Manifesto

/-!
# Hit-smallness statements charged on exact RG values

All uniform before choosing fields. Upper envelopes at labels valid; usable on Families
with anchored sum & optional marks. Initial gas. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Cash
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} {Z Z' : Support c} {L : Side}
variable {k k' : Finset ℕ} {w v : Air f G}
variable {V : Finset (Molecule S)} {b l d : ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (H : Cash W α μ L Q o C T R) (X : Coat T F) (hk : X.x=α) (he : X.width=o.K)

def numP (s : Molecule S) := ∑ i∈s,Mixed.shares S i

-- value on real sector, x from H
def emerging (_H : Cash W α μ L Q o C T R) (X : Coat T F) := proceedsA R X W o.a Q.halo Q.table

lemma ours_pos (m k r : ℕ) (u : ℝ) (s : Molecule S) : 0 ≤ H.ours m k r u s := by
  unfold ours; split
  next => exact H.price_nn ..
  next => exact le_rfl

include hk
lemma residency (p : Molecule S) (h : H.emerging X p≠0) :
    Ac.Spark H.supportP p ∧ troupe T R Q.halo (radiusB α) p ∧ (H.unionP p).Nonempty ∧
      (roster p).flags=RG.flags (Pressure.temp X.x) X.V∩H.unionP p := by
  unfold emerging proceedsA at h; split at h
  next hz =>
    have he' : X.B=radiusB α := congr_arg radiusB hk
    rcases hz with ⟨hy,hv,hp⟩; rw [he'] at hv hp hy
    refine ⟨hy,hv,?_,hp.symm⟩
    obtain ⟨i,hi⟩ := hy.1
    have hl : (H.supportP i).Nonempty := by
      rcases i with i|i|i|i
      · have hh := (hv.1.checkpoints _ (mem_toLeft.mpr hi)).1
        obtain ⟨v,hx⟩ := hh
        refine ⟨anchor S v,?_⟩
        exact halo_subset _ i.place (Packets.place_reads S i ▸ mem_biUnion.mpr ⟨v,hx, contains ..⟩)
      · let p:= (R.activities.forced i)
        obtain ⟨j,h⟩ := p.inventory_ne
        refine ⟨S.ratio.parent j,?_⟩
        exact halo_subset _ _ (mem_image_of_mem _ (show j∈ RG.inspected p.support from mem_union_left _ (p.inventory_sup h)))
      · exact exChart ..
      exact ⟨_,crucial S i ..⟩
    exact hl.mono (subset_biUnion_of_mem H.supportP hi)
  next hz => exact (h rfl).elim

include he
lemma unitQ (p : Molecule S) : ‖amountP R X W o.a Q.halo Q.table p‖ ≤ ∏ i∈p,H.text i := by
  let P:= planted X p
  have he k : ‖(P.taggedL k).attains R Q.table W o.a (own p) Q.halo p‖≤ ∏ i∈p,H.text i := (norm_integral_le_integral_norm _).trans
    (H.statements (P.taggedL k) hk he (planted_valid X p) ..)
  let v : ℝ := Fintype.card S.Choices; have hp : 0<v := by unfold v; positivity
  unfold amountP levelMean likely; rw [norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
  apply le_trans (mul_le_mul_of_nonneg_left (norm_sum_le ..) (inv_nonneg.mpr hp.le))
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=univ) (fun k _ => he k)) (inv_nonneg.mpr hp.le)).trans_eq
  rw [sum_const,nsmul_eq_mul,card_univ]; exact inv_mul_cancel_left₀ hp.ne' _

lemma anyF (q : Molecule S) (k : ℕ) : ‖H.emerging X q‖*(1+H.shapeW q)^k ≤ H.ours 0 k 0 0 q := by
  by_cases hp : H.emerging X q=0
  · rw [hp,norm_zero,zero_mul]; exact H.ours_pos ..
  have hv := (H.residency X hk q hp).1
  rw [ours, if_pos ((H.attends q).2 hv)]
  unfold emerging proceedsA; split
  next => exact mul_le_mul_of_nonneg_right (H.unitQ X hk he q) (by have ht:= H.positive_volume q; positivity)
  next h => rw [norm_zero,zero_mul]; exact H.price_nn ..



lemma pick (m i r : ℕ) (p : Molecule S) (hm : m ≤ p.card-1) (hr : r≤ numP p) (u : ℝ) (ht : u ≤ H.shapeW p) :
    ‖H.emerging X p‖*(1+H.shapeW p)^i ≤ H.ours m i r u p := by
  by_cases hz : H.emerging X p=0
  · rw [hz,norm_zero,zero_mul]; exact H.ours_pos ..
  have he' := (H.residency X hk p hz).1
  apply (H.anyF X hk he ..).trans_eq; rw [ours,ours,if_pos ((H.attends p).2 he'),if_pos
    (show H.ticketsP m r u p from ⟨he',hm,hr,ht⟩)]

lemma scripts_hit (U : Molecule S→ Prop) (m j r : ℕ) (t : ℝ) (h : ∀ p,U p → m ≤ p.card-1 ∧ r≤numP p ∧ t ≤ H.shapeW p) :
    Ac.Hit H.unionP (radiusB α) (fun i=> if U i then ‖H.emerging X i‖*(1+H.shapeW i)^j else 0) Q.exp (H.faresP.ceiling m j r t) := by
  apply Labels.raise_prices (H.unionP) (radiusB α) (fun i=> ?_) (H.charged m j r t)
  · intro i; split
    next he' => exact H.pick X hk he m j r i (h i he').1 (h i he').2.1 t (h i he').2.2
    exact H.ours_pos ..
  split
  next => exact mul_nonneg (norm_nonneg _) (by have := H.positive_volume i; positivity)
  exact le_rfl

omit hk he H in
lemma forced_cost (i : Molecule S) (h : (roster i).flags.Nonempty) : 1 ≤ numP i := by
  obtain ⟨j,hj⟩ := h; let s : Seed S := Sum.inr (Sum.inr j)
  have hv : s∈ Packets.seeds S (roster i) := by simp [s,Packets.seeds,hj]
  rw [register] at hv; obtain ⟨x,hx,hv⟩ := mem_biUnion.mp hv
  apply le_trans _ (Finset.single_le_sum (f:=Mixed.shares S) (fun i _=>Nat.zero_le _) (mem_toLeft.mp hx))
  change 0<x.shares; rw [← seeds_card]; exact Finset.card_pos.mpr ⟨_,hv⟩


end YM.ConnectedActivityE6.Cash
