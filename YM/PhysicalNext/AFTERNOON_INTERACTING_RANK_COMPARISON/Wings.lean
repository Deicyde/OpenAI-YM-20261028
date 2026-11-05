import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Accumulator
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Sight
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.TiltField
import YM.SectorNext.RECONNECTED_LOCALITY.Lodge

/-! # Pulled-back marks on the *nonlinear* argument, all layouts and stencils

All W, not just predictors on short clusters. Separated from Pole costs
because the compiler runs through every sector record incl frozen queries,
not only pose/nohole. Full positive-bond convention exactly. Zoom halo also
pays indicator reads.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure RG Filter MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker
     YM.PhysicalNext.PhysicalGuard7f546 Curved
     AnalyticBridge.LocalGaussianLaws Exterior Remote Lift Local
     AnalyticBridge.RelativeLogdet AnalyticBridge.MarginalMultiplier3b1d Rows
     Precision Next.Fluctuations Wisps Current
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
    {x β τ : ℝ} {X : Support c} {Y : Support f}
    {P : Teller G} {A A' : Stores S} {F : Forest S.ratio} {k l : S.Choices} {U V : Config G c}

lemma read_gaze (L : Lantern G S) {k l : Streak L.park} {p : Nearby X U V A A' k l} {y : RoomView A x k.wood G} {z : RoomView A' x l.wood G}
    (hv : nearby X y=amplify p z) (hp : Boosted T P x) (i : Bond f) (h : Shields X (S.ratio.parent i.1) (25*radiusB x+20)) :
    gazed T k.tag L.χ U x β L.hood y i = gazed T l.tag L.χ V x β L.hood z i := by
  let F:=k.wood; let B:=l.wood
  let o := S.ratio.parent i.1
  let M:=radiusB x
  have hl : lumen S x X i:=h.shrink (by omega)
  have hs : PatchReads.Scan S x o M A A' F B k.tag l.tag U V y.1 z.1 := by
    apply p.shutter (h.shrink (by omega))
    intro j j' he hj; exact Nearby.iced hv _ (h.shift (by omega)) j' hj
  let H:= portrait T A F k.tag x U .endpoint L.χ L.hood y.1
  let H':= portrait T A' B l.tag x V .endpoint L.χ L.hood z.1
  let a:=tape (H+coupling β • y.2);let b:=tape (H'+coupling β • z.2)
  change physical _ _ U y.1 a i=physical _ _ V z.1 b i
  by_cases ht : i∈ F.trunks
  · exact (F.on_tree _ ⟨i,ht⟩).trans (B.on_tree _ ⟨i,(p.trunk_iff _ h.center).mp ht⟩).symm
  let u : F.Free:=⟨i,ht⟩; let u₂ : B.Free:=⟨i,mt (p.trunk_iff i h.center).mpr ht⟩
  have hr : replica S.ratio U i= replica S.ratio V i:= PatchReads.rep_share hs.outer i (by change separation o o ≤ M; simp)
  unfold physical; refine (F.off_tree _ u).trans (Eq.trans ?_ (B.off_tree _ u₂).symm)
  by_cases hc : chill A x F u
  · let v : Frozen A x F:=⟨u,hc⟩; let v':Frozen A' x B:=⟨u₂,(p.frozen (i:=u) hl rfl).1 hc⟩
    exact Eq.trans (freeze_held F _ _ _ (j:=v)) ((Nearby.iced hv v hl v' rfl).trans (freeze_held B _ _ _ (j:=v')).symm)
  let w:Active A x F:=⟨u,hc⟩
  let w':Active A' x B:=⟨u₂,mt (p.frozen (i:=u) hl rfl).2 hc⟩
  have he : a w = b w' := by
    ext j
    change H (w,j) + coupling β * y.2 (w,j)= H' (w',j)+ coupling β*z.2 (w',j)
    rw [Nearby.flammable hv w hl w' rfl]
    apply congr_arg (fun x=>x+_)
    unfold H H'; simp_rw [← mean_endpoint]
    exact PatchReads.mean_eq hp.ready (hs.lower (by omega)) rfl
  have h1 : returned A F U y.1 a u=G.lieExp (a w)*replica S.ratio U i:= freeze_regular (j:=w) ..
  have h2 : returned A' B V z.1 b u₂=G.lieExp (b w')*replica S.ratio V i:= freeze_regular (j:=w') ..
  exact h1.trans ((congr_arg₂ HMul.hMul (congr_arg G.lieExp he) hr).trans h2.symm)

def wings (S : StepData c f) (W : ℕ) (Y : Support f) := halo W (Y.image S.ratio.parent)
lemma involved (W : ℕ) (x : Site f) (hx : x∈Y) : S.ratio.parent x∈wings S W Y := halo_subset W _ (mem_image_of_mem _ hx)
lemma direct_beam {x : ℝ} {i : Site f} {B : ℕ} (H : 25*radiusB x+30 ≤ B) (hp : i∈ halo 8 Y): Shields (wings S B Y) (S.ratio.parent i) (25*radiusB x+20) := by
  obtain ⟨j,hj,hv⟩:= halo_spec.mp hp
  have hh : separation (S.ratio.parent j) (S.ratio.parent i) ≤ 9 := by
    apply Nat.le_of_mul_le_mul_left _ S.ratio.count.property
    apply (Corona.foreshorten S.ratio j i).trans
    have h : 1 ≤ S.ratio.count.val:= S.ratio.count.property; change separation j i+S.ratio.count.val ≤ S.ratio.count.val*9; omega
  exact Shields.shift (o:=S.ratio.parent j) (t:=B) (fun k hk=>halo_spec.mpr ⟨_,mem_image_of_mem _ hj,hk⟩) (by omega)

lemma forage {C : Type*} [MeasurableSpace C] (hp : Boosted T P x) (L : Lantern G S)
    (τ : ℝ) (g : Config G f→ C) (hg : UsesFinal τ Y g) (ht : Measurable g) (h : GaugeInvariant g) (B : ℕ)
    (hh : 25*radiusB x+30 ≤ B) (q : ℝ) (β : ℝ) : Sees (fun A k U z=> g (gazed (A:=A) T k.tag L.χ U x β L.hood z) : Shader G S x L.park C) (wings S B Y) False q := by
  constructor
  · intro A k; obtain ⟨p,hp,H⟩:=gazed_tag hp L β A k; exact ⟨g ∘ p,ht.comp hp,fun V hv a=> congr_arg g (H _ hv a).symm⟩
  · intro A A' U V k l ha hb hv hw a b hr; exact (UsesFinal.allReads _ Y g hg) _ _ fun i hi _=> read_gaze L hr hp i (direct_beam hh (Thirst.inspect Y hi))
  intro A U k v hU b; rw [← winding A k.wood x β L.hood U T hp.funded v k.tag L.χ b (hp.fogged _ _ _ _ (hU.turn v))]; exact (h ..).symm
lemma shade_pure {θ : ℝ} {i : Site f} {W} (L : Lantern G S) {x : ℝ} {k l:Streak L.park} (p : Nearby X U V A A' k l) (u : RoomView A x k.wood G) (v : RoomView A' x l.wood G)
    (hz : nearby X u=amplify p v) (h : ∀ j∈ parasol i W, lumen S x X j): InteractingRank.shade A k.wood θ β L.χ i W u=InteractingRank.shade A' l.wood θ β L.χ i W v := by
  let Z:= parasol i W
  let f (A B : Stores S) (U V) (k l:Streak L.park) (hp : Nearby X (U : Config G _) V A B k l) (i : Curved.Window A k.wood x Z) : Curved.Window B l.wood x Z:= ⟨⟨⟨i.val.val.val,mt (hp.trunk_iff _ (h _ i.property).center).mpr i.val.val.property⟩, fun he=>i.val.property ((hp.frozen (i:=i.val.val) (h _ i.property) rfl).2 he)⟩,i.property⟩
  let e:= (Equiv.mk (f A A' U V k l p) (f A' A V U l k p.back) (fun _=>rfl) (fun _=>rfl))
  unfold InteractingRank.shade Curved.veil; refine Fintype.prod_equiv e _ _ fun i=>?_
  apply congr_arg; apply PiLp.ext; intro a; exact Nearby.flammable hz i.val (h _ i.property) (e i).val rfl a

lemma shade_sees {θ : ℝ} {i : Site f} {W B} (L : Lantern G S) (hp : 25*radiusB x+30 ≤ B) :
    Sees (fun A k _ y=>InteractingRank.shade A (Streak.wood k) θ β L.χ i W y : Shader G S x L.park ℝ) (wings S B (Spindle.patch W i)) False τ := by
  refine ⟨fun A k => ⟨fun y => InteractingRank.shade A k.wood _ _ _ _ _ y.2,?_,fun _ _ _=>rfl⟩,fun p q h _ u v hz=> shade_pure L h u v hz ?_,?_⟩
  · exact ((Curved.veil_smooth (G:=G) (A:=A) (x:=x) (F:=k.wood) (parasol i W) L.χ (haze G θ β S.patch.L)).continuous.measurable.comp measurable_snd).comp measurable_snd
  · intro j hj; refine (direct_beam hp (show j.1∈ halo 8 (Spindle.patch W i) from ?_)).shrink (by omega)
    have he: j.1∈Spindle.patch (W+8) i := (Finset.mem_filter.mp hj).2.1
    have hX:= Corona.line_dist i j.1 0 W (by omega); have hx:= Corona.line_dist i j.1 W (W+8) (by omega)
    rw [Corona.line_end i j.1 ((Spindle.doors _).mp he)] at hx
    rw [Corona.line_home, Nat.sub_zero] at hX; exact halo_spec.mpr ⟨_,(Spindle.doors _).2 hX,hx.trans (by omega)⟩
  intro A V k v hm a; unfold InteractingRank.shade Curved.veil
  exact Finset.prod_congr rfl fun i _=> by dsimp only [rotate_bus]; rw [Curved.turn_color]; unfold Next.SectorChange.broad;rw [G.norm_adjoint]
end YM.PhysicalNext.InteractingRank
