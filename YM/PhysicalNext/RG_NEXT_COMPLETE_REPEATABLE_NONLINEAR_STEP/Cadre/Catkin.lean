import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Expanse
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Toll
/-! # F-averaged restoration (port of Powder, using integrated average and actual K support).
 Existing terms are single-F; they are not multiplicative across average! Use this version.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Cash
open PhysicalNext.Repeat.Greenbelt PhysicalNext.Repeat
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Gas Ursell Trees Multiple Letter OmitClusters
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C δ e : ℝ} {R : Rep G f} {Z Z' : Support c} {L : Side}
variable {k k' : Finset ℕ} {w v : Air f G}
variable {j b l d : ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (H : Cash W α μ L Q o C T R) (χ : Chi) (V : Config G c)
variable (p : Renewed j a δ e H)

def colognePool : H.Chapter→ℝ := Sum.elim (H.depositsPool χ V) fun i=> -(H.trainedPool χ V i)

def truthfulPool (c : H.Chainbook) := if H.Fresh c ∧ H.inventory c.1.toLeft=RG.flags (Pressure.temp α) V then
    manyW (H.colognePool χ V) c else 0

lemma truthPool (A : Finset H.ThickP) (s : Reps H.fragrances) :
    H.truthfulPool χ V (hint (A,s))=H.bankedPool χ V A*manyW (fun i=>-(H.lossesPool χ V A i)) s := by
  let Z:= H.tall A
  let f i:= H.trainedPool χ V i
  let g i := H.lossesPool χ V A i
  let c := hint (A,s)
  have hh : c.1.toLeft=A := toLeft_disjSum ..
  have hx : c.1.toRight=s.1 := toRight_disjSum ..
  have hv i : g i= if Disjoint Z (H.bookFoot (.inr i)) then 0 else f i := rfl
  unfold truthfulPool; rw [hh]
  by_cases he : H.inventory A=RG.flags (Pressure.temp α) V
  swap; · unfold bankedPool; rw [if_neg (fun h=>he h.2),if_neg he,zero_mul]
  by_cases h : Gas.separated (blocked H.largeAt) A
  swap
  · unfold bankedPool Gas.value; rw [if_pos he,if_neg h,if_neg (fun hz=> h (hh ▸ hz.1.2.1)),zero_mul]
  unfold bankedPool Gas.value; rw [if_pos he,if_pos h]
  by_cases hk : ∀ i∈s.1, ¬Disjoint Z (H.bookFoot (.inr i))
  · have hn : H.Fresh c := ⟨hinter _, hh.symm ▸ h,fun i hi=> (by rw [hh]; exact hk i (hx ▸ hi))⟩
    rw [if_pos ⟨hn,he⟩, colognePool, Letter.hint_price]; refine congr_arg _ ?_
    unfold manyW; apply prod_congr rfl; intro i _; dsimp only; rw [show H.lossesPool χ V A i.val=f i.val from (hv i.val).trans (if_neg (hk i.val i.2))]
  rw [if_neg (fun hn=> hk (fun i hi=> (show ¬ Disjoint (H.tall A) _ from hh ▸ hn.1.2.2 i (hx.symm ▸ hi)))), manyW]
  push Not at hk; obtain ⟨i,hi,hk⟩ := hk
  rw [Finset.prod_eq_zero (s:=univ) (i:= (⟨i,hi⟩:↥s.1)) ?_ ?_,mul_zero]
  · simp
  change (-g i)^_/ _=0; rw [hv,if_pos hk]; simp

include p
lemma savablePool : Summable (H.truthfulPool χ V) := by
  have hk' := H.first_logsPool χ V p
  have hv : Summable (H.trainedPool χ V) := ((price_log H.seam (H.entriesPool χ V) H.hardH H.smallAt (radiusB α) H.testS
    (add_nonneg p.full p.post.le) hk').2.1.2.1).of_norm
  have hg : Summable (H.depositsPool χ V) := by
    have hs (p : H.ThickP) : 0 ≤ H.broadPay j p := H.ours_pos ..
    have hz (i : H.ThickP) : (H.largeAt i).Nonempty := i.2.1
    have hx := AbsoluteSums.Product.everyone_ne _ _ hs (fun i _=>hz i) p.marks
    refine Summable.of_norm_bounded hx.2.1 fun i => ((H.renew χ V j).2 i).trans (le_mul_of_one_le_right (hs i) ?_)
    exact Real.one_le_exp (mul_nonneg (add_nonneg p.full p.post.le) (Nat.cast_nonneg _))
  have hs := (concert (show Summable (H.colognePool χ V) from Summable.sum _ hg hv.neg)).summable
  apply Summable.of_norm_bounded hs.norm; intro i; unfold truthfulPool; split
  · exact le_rfl
  rw [norm_zero]; exact norm_nonneg _

variable (O : Tree.Forest S.ratio)
lemma bouquetPool : HasSum (fun c : H.Chainbook=> overhead (prism T α χ o.K V O) R Q.table * H.homesteadPool χ V * H.truthfulPool χ V c) (S.push R.beta R.eval V) := by
  let K:= overhead (prism T α χ o.K V O) R Q.table; let f c := K * H.homesteadPool χ V*H.truthfulPool χ V c
  have hg (A : Finset H.ThickP) : HasSum (fun v=> f (hint (A,v))) (overhead (prism T α χ o.K V O) R Q.table * H.siegePool χ V A) := by
    have he' := missing_tail H.smallAt (H.tall A) (radiusB α) (H.entriesPool χ V) (fun i=> i.2.1) (add_nonneg p.full p.post.le)
      (H.first_logsPool χ V p) 0
    simp only [Nat.zero_le,↓reduceIte] at he'
    have hz : Summable (H.lossesPool χ V A) := he'.2.1.of_norm
    have hy := (concert hz.neg).mul_left (K*H.homesteadPool χ V * H.bankedPool χ V A)
    convert! hy using 1
    · funext i; unfold f; rw [H.truthPool χ V]; ring
    unfold siegePool; rw [tsum_neg]; unfold K; ring
  have ht : Injective (@hint H.ThickP H.fragrances) := LeftInverse.injective (show LeftInverse Letter.hidden hint from
    (tracks (κ:=H.fragrances) (ι:=H.ThickP)))
  have hv : Summable (f∘hint (ι:=H.ThickP)) := ((H.savablePool χ V p).mul_left _).comp_injective ht
  apply (ht.hasSum_iff (f:=f) ?_).1
  · rw [← (H.rampartPool χ V p O).tsum_eq]; simp_rw [← (hg _).tsum_eq];
    exact (show (∑' i,(f ∘ hint (ι:=H.ThickP)) i)= _ from hv.tsum_prod) ▸ hv.hasSum
  intro i hp; unfold f truthfulPool; rw [if_neg (fun hx=> hp ⟨Letter.hidden i,Letter.unruly _ hx.1.1⟩),mul_zero]



end YM.ConnectedActivityE6.Cash
