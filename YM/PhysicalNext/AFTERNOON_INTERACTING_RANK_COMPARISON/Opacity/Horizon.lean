import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.Read
import YM.AnalyticBridge.GAUSSIAN_INTERIOR_COMPARISON.FlatData
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Throne
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Attic
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Rebate
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Wiggle


/-!
# Each smooth-side selected row through the true column, value estimate

Including a kept-side equality with threshold t under Seeded
(see use in Fees giving `fiery`/2 ≤ t; pledges not unconditional). No
germs asserted. Also prove controls to catch both fine and interface chargedUp
positions in curb remotely. Not an estimate of whole scalar remainder.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Milk
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
     PhysicalGuard7f546.Curved AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian Wisps AnalyticBridge.Annulus1AD Oriented
open AnalyticNext.ConnectedActivity
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {A : Stores S} {F : Forest S.ratio}
    {V : Config G c} {P : Teller G} {T : Tube G S} {i : Site c} {x β d t C : ℝ} {U : Config G f}
-- Awake at CAB tests
lemma halo_stops (q : Chi) (W : Prices G (Active A x F)) (Y : LinkArray G (Frozen A x F))
    (h : 0<radiusB x) (he : 0 ≤ C) (hi : i ∉ A.dome (100*radiusB x))
    (hp : ∀ u:Active A x F,separation i (Aff.home S u.val.val)≤radiusB x → ‖tape W u‖ ≤ C) :
    Aff.Stops S (basisArray x A F q d V Y W) V (AnalyticBridge.Annulus1AD.landed x A F V Y W) i (radiusB x) C:=by
  let a:=basisArray x A F q d V Y W; let U:= AnalyticBridge.Annulus1AD.landed x A F V Y W
  have he' j (hj : separation i (Aff.home S j) ≤ radiusB x) : U j = increment (replica S.ratio V) a j ∧ ‖a j‖ ≤ C:= by
    rcases Aff.environs F A x j _ i hi (by omega) with hF|hF
    · rw [increment, show a j=0 from wood x A F q d V Y W j hF, G.mat_lieExp_zero,show replica S.ratio V j=1 from if_pos (F.trunk_internal hF), show U j=1 from F.on_tree _ ⟨j,hF⟩,norm_zero, one_mul]; exact ⟨rfl,he⟩
    let p:=fundedB (x:=x) j hF
    have ht:a j=tape W p:= clear_basis x A F q d V Y W p
    rw [increment,ht]; exact ⟨clear_physical x A F V Y W p,hp p hj⟩
  exact ⟨fun j hj=> (he' j hj).2,fun j hj=>(he' j hj).1⟩

-- pay if on intact; doesn't descend to extension needing Seeds globally
lemma still_kept (P : Teller G) (D : Patch) : ∀ᶠ x in atTop,∀ {c f : Side} (S : StepData c f) (T : Tube G S) (A : Stores S), S.patch=D → P.Funds S T →
      ∀ (U : Config G f) k (V : Config G c) W t, Seeded A U k V x W → (fiery G x S.patch.L)/2 ≤ t →
       ∀ y : Cell f, S.ratio.parent y.1∉ A.dome (2*radiusB x) → PathData.kept T.high t y.1 U:=by
  filter_upwards [Wax.reserve_lane G D.L P.top.clip.relaxation P.top.clip.radius_pos] with x ht c f S T A hS hT U k V W t h ht' i hi
  have hq : 0≤t:= (div_nonneg (temp_nonneg _) (by norm_num : 0 ≤ (2:ℝ))).trans ht'
  have hj : LaneCounts T.up x t T.high (Work.E04.capacity P.top) 1 S.ratio.parent:= by
    obtain ⟨a,c,H,-⟩:=hT.feeds
    rw [hT.high]
    apply Work.E04.lanes H le_rfl hq one_pos (Work.E04.parent_separation _)
    refine ⟨ht.1,fun p h=> ht.2 _ ?_⟩; rw [← hS]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right ht' (Real.exp_pos _).le) h
  intro j; by_contra! he
  have hv : t*Real.exp (separation i.1 j.1/T.high.relaxation)<toll U j:=he
  have h': S.ratio.parent j.1∉ A.place:=fun hh=>hi (halo_spec.mpr ⟨S.ratio.parent j.1,hh,by rw [separation_comm]; have h:=hj.dropped U _ _ hv; omega⟩)
  have hu : t ≤ t*Real.exp (separation i.1 j.1/T.high.relaxation):= le_mul_of_one_le_right hq (Real.one_le_exp (div_nonneg (Nat.cast_nonneg _) T.high.radius_pos.le))
  exact ((SectorNext.Remainder.exterior_fine h h').trans ht').not_gt (hu.trans_lt hv)
lemma reelF (T : Tube G S) (s : Signed) (i : Cell f) (V : Config G c) (U : Config G f) (k : S.Choices) (t x : ℝ)
   (hf : PathData.kept T.high t i.1 (pull s 0 U)) (hY : PathData.kept T.high (fiery G x S.patch.L) i.1 (pull s 0 U)) :
    T.workF (till x) (pull s 0 U) (pull s 0 V) t (temp x) i=Aff.Fextend T x k s i V U := by
  have hh v (h : PathData.kept T.high v i.1 (pull s 0 U)) : G.chord (faceValue (pull s 0 U) i) ≤ v:= by
     simpa only [separation_self,Nat.cast_zero,zero_div,Real.exp_zero,mul_one] using h i
  rw [← Aff.work_expandF T x k s i V U hY]; unfold Tube.workF crown trunk PathData.clipped
  rw [if_pos hf,if_pos hY,if_pos (hh _ hf),if_pos (hh _ hY)]
lemma rim_taken (hc : 1<c.val) (hB : 0<radiusB x) (i : Where S) (F : Forest S.ratio) (p : Signed) (hp : p.act (roots S i) ∉ A.dome (50*radiusB x)) : curb (shots S x) A F x p i:= by
  obtain ⟨e,he⟩:= AnalyticBridge.GaussianInterior.FlatData.crosses_at S hc F (p.act (roots S i))
  have hz := Aff.environs F A x e.val _ _ hp (by rw [Aff.home,he, separation_self]; omega)
  refine ⟨⟨e,(stillActive ..).1 (hz.resolve_left e.property)⟩, (contains ..).2 ?_⟩; rw [he,separation_self]; omega

section w
lemma fronts (P : Teller G) (D : Patch) (hD : D.Branches P.bind G) (hC : Aff.Reserve P C) :
  ∀ᶠ x in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=D → P.Funds S T→ ∀ (A : Stores S) (V : Config G c),
    Aff.cert S x A V → ∀ (F : Forest S.ratio) (p : Slots S) k q (d : ℝ) (Y : LinkArray G (Frozen A x F)) (a : Prices G (Active A x F)),
     let U:= AnalyticBridge.Annulus1AD.landed x A F V Y a
     let w:= basisArray x A F q d V Y a
     let o:= Aff.base S p
     Aff.Stops S w V U o (radiusB x) (Rates.allowance G D x 1 7) → o∉ A.dome (50*radiusB x) →
       |Aff.squareOf (Aff.target T (till x) (temp x) p k V U)-Aff.squareOf (lands T x V k (shots S x) A F q d Y a p)| ≤ Rates.allowance G D x 3 34 := by
  filter_upwards [bump_at P D hD 7, Aff.arc_bill P C hC D hD 7 le_rfl, Aff.difference_pay G D 11 22,
     Rates.widen G D 2 (by decide : 12+7 ≤ 20), Rates.grow G D 2 (by decide : 20<22) 2] with x h hw hf hv he c f S T hS hT A V hA F p k q d Y a U w o hZ hp
  obtain ⟨h1,h2⟩:= hw c f S T hS hT V A F hA k U p w (fun h=>hp (Aff.placed A _ _ (by omega) h)) hZ
  let R:=till x; let B:= Rates.allowance G D x 2 20
  let X := Aff.target T R (temp x) p k V (replica S.ratio V) + Aff.derivative T R p V w
  apply hf _ _ h1
  apply (norm_sub_le_norm_sub_add_norm_sub _ X _).trans
  refine (add_le_add h2 (d:=B) ?_).trans (by linarith only [show 2*B ≤ _ from he])
  rw [norm_sub_rev]
  change ‖(Rows.base T x V k p+Rows.bump T x V k w p)-X‖≤B
  unfold X; rw [tallyBase, add_sub_add_left_eq_sub]
  exact (h S T hS hT A V hA p k w (fun h=>hp (Aff.placed A _ _ (by omega) h)) hZ.1).trans hv
end w
end YM.PhysicalNext.InteractingRank.Milk
