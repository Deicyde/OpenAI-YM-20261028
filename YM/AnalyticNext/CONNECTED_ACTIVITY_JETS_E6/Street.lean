import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Melt
import YM.Next.SCHEDULE.Flights

/-!
# Constrained/unconstrained species exact dependence, external one-time predicate

Do not assert `Regular` yet (needs extension/symmetries & derivatives).
Supply UsesFinal (depends on flags intersection). Unforced carries explicit
predicate not differentiated.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Gas Ursell Trees Multiple Letter OmitClusters
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C δ e : ℝ} {R : Rep G f} {Z Z' : Support c} {L : Side}
variable {k k' : Finset ℕ} {w v : Air f G} {j b l d : ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}

lemma inheritance {t : ℝ} {F : Config G c→ℝ} (he : UsesFinal t Z' F) (h : Z'⊆Z) : UsesFinal t Z F := by
  intro U V hu hp; apply he U V (agrees_mono hu (by exact_mod_cast h))
  rw [← Finset.inter_eq_left.mpr h, inter_assoc, hp, inter_assoc]

def vary (X : Coat T F) (V : Config G c) : Coat T F := {X with V:=V}

namespace Cash
variable (H : Cash W α μ L Q o C T R) (X : Coat T F) (hk : X.x=α) (he : X.width=o.K)
variable (p : Renewed j a δ e H)

include hk he
lemma emerge_uses (s : Molecule S) :
    UsesFinal (Pressure.temp X.x) (H.unionP s) (fun V=> H.emerging (vary X V) s) := by
  intro U V h hp
  let t:= Pressure.temp X.x
  let Y:= vary X U; let Y':= vary X V
  let Z:=planted Y s; let Z':= planted Y' s
  let q:= H.unionP s; have hl : ground R T Q.halo X.B s=q := by unfold Coat.B; rw [hk]; rfl
  have hh k : (Z.taggedL k).attains R Q.table W o.a (own s) Q.halo s=(Z'.taggedL k).attains R Q.table W o.a (own s) Q.halo s := by
    refine H.vista s (Z.taggedL k) (Z'.taggedL k) hk he (planted_valid Y s) (planted_valid Y' s) ?_ (fun _ _=> Iff.rfl)
    apply Village.mk
    · change X.x=X.x; rfl
    · change X.width=X.width; rfl
    · change X.χ=X.χ; rfl
    case actual => exact h
    case frames => intro i h; change X.Y i=X.Y i; rfl
    case site => intro i hi; change Prod.fst k i=_; rfl
    case bond => intro i hi; change Prod.snd k i=_; rfl
    intro i hi
    have he : i ∈ q ∩ RG.flags t U ↔ i∈q∩RG.flags t V := by unfold t q; rw [hp]
    have hv : i∈RG.flags t U ↔ i∈ RG.flags t V := by simp only [mem_inter,show i∈q from hi,true_and] at he; exact he
    change i∈(planted Y s).seeds.place ↔ i ∈ (planted Y' s).seeds.place
    simp only [planted,vary,Y,Y',preps,place,mem_union,t] at hv ⊢; rw [hv]
  have hz : standsIn Y R Q.halo s ↔ standsIn Y' R Q.halo s := by
    unfold standsIn claimed
    change Ac.Spark (areas R T _ X.B) s ∧ troupe T R Q.halo X.B s ∧ RG.flags t U∩ground _ _ Q.halo X.B s=_ ↔
      Ac.Spark (areas R T _ X.B) s ∧ troupe T R Q.halo X.B s ∧ RG.flags t V∩ground _ _ Q.halo X.B s=_
    rw [hl,inter_comm (RG.flags t U),inter_comm (RG.flags t V),show q∩_= q∩_ from hp]
  change (if standsIn Y R Q.halo s then _ else _)=(if standsIn Y' R Q.halo s then _ else _); rw [hz]; split
  next hk => exact congr_arg likely (funext hh)
  rfl

omit he in
lemma clean_claim (i : H.ThinP) :
    H.entries X i≠0 → Healthy (Pressure.temp X.x) (H.smallAt i) X.V := by
  intro hi
  have hp : RG.flags (Pressure.temp X.x) X.V ∩ H.smallAt i=∅ := (H.residency X hk _ hi).2.2.2.symm.trans i.2.2
  exact (disjoint_iff_inter_eq_empty.mpr hp).symm




omit he hk in
lemma rightful (r : H.Chainbook) (hi : H.smiles X r≠0) :
    H.states X r ∧ (H.inventory r.fst.toLeft).Nonempty := by
  unfold smiles at hi; split at hi
  next hz =>
    have he : OmitClusters.restores r := by
      obtain ⟨i,hh⟩ := hz.2.1.1; rcases i with i|i
      · exact ⟨i,hh⟩
      obtain ⟨x,hx,hv⟩:= not_disjoint_iff.mp (hz.1.2.2 i (mem_toRight.mpr hh)); obtain ⟨b,hb,ht⟩:= mem_biUnion.mp hx
      exact ⟨b,mem_toLeft.mp hb⟩
    obtain ⟨i,he⟩:=he
    refine ⟨hz.2.2,?_⟩
    obtain ⟨x,hx⟩:=i.2.2; exact ⟨x,mem_biUnion.mpr ⟨i,mem_toLeft.mpr he,hx⟩⟩
  exact (hi rfl).elim
omit he in
lemma cluster_good (r : H.fragrances) (h : H.trained X r≠0) : Healthy (Pressure.temp X.x) (H.bookFoot (.inr r)) X.V := by
  have he : (∏ i,H.entries X (r.2 i))≠0 := fun hh=> h (by unfold trained Gas.term; rw [hh,mul_zero,zero_div])
  apply Finset.disjoint_left.mpr; intro i hi hx
  obtain ⟨p,hp,hr⟩:= mem_biUnion.mp hi; exact Finset.disjoint_left.mp
    (H.clean_claim X hk (r.snd p) (fun hv => he (prod_eq_zero hp hv))) hr hx
end Cash
end YM.ConnectedActivityE6
