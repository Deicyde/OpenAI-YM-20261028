import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Symplex
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Unified

/-! # Vertex covariance (gauge) including log pre-stories, tag/frame/chart selection. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Cash
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll  
open Gas Ursell Trees    Rotation Hues
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f n : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} {L : Side}
variable {k k' : Finset ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (H : Cash W α μ L Q o C T R) (X : Coat T F) (hk : X.x=α) (he : X.width=o.K)
variable (hp : X.manifest) (l : Finset ℕ)

lemma wind (z : Site c→G.El) (hp : X.manifest) : (sluice X z).manifest := X.retains z hp

include hp hk he H
lemma scours (z : Site c→G.El) (w : Air f G) (i : Head S) : (sluice X z).vertex R Q.table W o.a l Q.halo
      (weep X z w) i=X.vertex R Q.table W o.a l Q.halo w i := by
  let Y:=sluice X z; let V:=weep X z w; let u:=X.liftA R.beta w; let v:=Y.liftA R.beta V
  have hs := H.laws.data
  have ht : ShellAccess S G X.x W X.width o.γ := by rw [hk,he]; exact hs.access
  have hf := H.laws.intake.ready
  have hh := (hs.localP F X hk he hp).sails; have hF := (hs.localP F Y hk he (wind X z hp)).sails
  have hu : v=spinRow S z u := fullA X z hf ht R.beta w
  have hx p : Y.condensation p=X.condensation p := drip X z hf hh hF p
  have hq (d) (p : Finset (Bond f)) : Y.enforce d v p=X.enforce d u p := by rw [hu]; exact Hues.mandate X z ..
  have hV i : Y.gentry Q.table o.a v i=X.gentry Q.table o.a u i :=
    price_halo X z hf ht R.beta o.a w Q.table_exists hh.room (mul_pos o.large hh.room.fiery) (by unfold t; rw [hk,hs.funds.length_eq]; exact hs.covers) i
  let hv := X.plaza
  have hg (s : Signed) j : Y.debit v s j=X.debit u s j ∧ Y.light v s j=X.light u s j ∧ Y.extracted Y.μ s j=X.extracted X.μ s j := by
    rw [hu]; obtain ⟨he,hj,-⟩ := rainWorks X z hf ht u s j; refine ⟨he,hj,?_⟩
    rw [(slopeC X z hf ht).2]; exact (rainWorks X z hf ht X.μ s j).2.2
  have hT := funds_branch hf
  rcases i with A|i|i|i
  · change (if Packets.connected S Q.halo X.B A then Y.Pack R Q.table l W o.a A v else 0)=
      (if Packets.connected S Q.halo X.B A then X.Pack R Q.table l W o.a A u else 0)
    split
    next =>
      have hz : Y.existSeeds A 300↔ X.existSeeds A 300 := by unfold existSeeds Y sluice rinse wrapY Coat.B; dsimp only; rw [RG.gauge_flags]
      unfold Coat.Pack; rw [hz]; split
      next =>
        let b:= 300 * X.B; let T:= A.dome (304*X.B)
        have hh₁ : Y.steamLog R Q.table o.a A v=X.steamLog R Q.table o.a A u := by
          have hc : Y.quoteNear A v=X.quoteNear A u := congr_arg Oriented.averaged (funext fun s=>
            Finset.sum_congr (show posted (turnStore s A) (200*Y.B)=posted (turnStore s A) (200*X.B) from rfl)
              (fun j _=> (hg s j).1))
          have ha : Y.far_bills A=X.far_bills A := congr_arg averaged (funext fun s=>
            Finset.sum_congr (show posted (turnStore s A) (200*Y.B)=posted (turnStore s A) (200*X.B) from rfl)
              (fun j _=> (hg s j).2.2))
          have hj : (∑ i∈ hv T,Y.gentry Q.table o.a v i)= ∑ i∈ hv T,X.gentry Q.table o.a u i := Finset.sum_congr rfl (fun i _=> hV i)
          have hx' : (∑ p∈visit A (200*Y.B), Y.condensation p)=∑ p∈ visit A (200*X.B), X.condensation p := Finset.sum_congr rfl (fun p _=> hx p)
          unfold steamLog; rw [hc,ha,hx']; change _+(∑ i∈hv T,Y.gentry Q.table o.a v i)-_=_+(∑ i∈hv T,X.gentry Q.table o.a u i)-_; rw [hj]; rfl
        have hZ : Contract.order R l (vias S A b) (Y.input v)*tickets A b (Y.input v) X.k*profiles A X.χ b X.x W (Y.input v) X.k (gauge z X.V) =
            Contract.order R l (vias S A b) (X.input u)*tickets A b (X.input u) X.k*profiles A X.χ b X.x W (X.input u) X.k X.V := by
          have hh p : Y.rawStorm v W A R l p=X.rawStorm u W A R l p := by rw [hu]; exact storm_g X z u hT ..
          have hx := Y.forceds A R l W v; dsimp only at hx; simp_rw [hh] at hx
          exact hx.symm.trans (X.forceds ..)
        unfold steam; dsimp only; rw [hh₁, show Y.enforce o.a v (Y.plaza (A.dome (304*Y.B)))= _ from
          hq o.a (X.plaza T)]
        apply congr_arg₂ (·*·) _ rfl
        rw [mul_assoc] at hZ
        simp_rw [mul_assoc]; change _*(Contract.order R l (vias S A b) (Y.input v)*(tickets A b (Y.input v) X.k*profiles A X.χ b X.x W (Y.input v) X.k (gauge z X.V)))=_; rw [hZ,mul_assoc]
      rfl
    rfl
  · have hv : R.activities.K i (Y.input v)= R.activities.K i (X.input u) := by
      rw [hu,banks X z u]; exact H.laws.intake.cap.labels.forced.sym ..
    exact congr_arg₂ (·*·) hv (hq (2*o.a) (X.plaza (forcedFoot S.ratio 0 X.B R i)))
  · change Real.exp _-1=Real.exp _-1; apply congr_arg (fun a=> Real.exp a-1)
    rcases i with i|i|i
    · change Y.inhale R o.a v i=X.inhale R o.a u i; rw [hu]; exact inhalesG X z u (hk.symm ▸ H.laws.intake) ..
    · rcases i with i|i|i
      · change (if Inside _ X.seeds (200*X.B) then 0 else -R.beta*Raw.orientation*(Y.enforce (2*o.a) v (X.booth (rowSite S i))*Y.light v i.1 i.2 + Y.extracted Y.μ i.1 i.2))= X.speck u R.beta o.a i
        unfold speck; rw [hq, (hg i.1 i.2).2.1,(hg i.1 i.2).2.2]
      · change (if voyage X.seeds (200*X.B) i then 0 else Y.condensation i)=X.undercurrent i; unfold undercurrent; rw [hx]
      change (if i∉_ ∧ X.Hot i then Y.gentry Q.table o.a v i else 0)= X.solo u Q.table o.a i; unfold solo; rw [hV]; rfl
    rcases i with i|i|i|i|i
    · exact congr_arg (fun x=> -x/2) ((porous X z hf hh hF).1 i)
    · exact congr_arg (fun A=> ArmA X.shutter A i/2) (neutral Y X rfl)
    · exact congr_arg (fun x=> x/2) ((porous X z hf hh hF).2 i)
    · exact Hues.influence X z hf ht ..
    exact Hues.joinsD X z hf ht ..
  change Y.detect v W o.a R l i=X.detect u W o.a R l i; rw [hu]; exact flags_g X z u hT ..
end YM.ConnectedActivityE6.Cash
