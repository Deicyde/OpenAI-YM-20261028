import YM.Planned.PRIMARY_INTEGRAL_295.Mowing
import YM.Planned.PRIMARY_INTEGRAL_295.Night
/-!
# Auditing numerical cone of no-hole dark K

True torus V without Omni. D,F0 entries at K.Areas require kernel FINITE
range; origin computed with AFFINE turns, dL. No predicate, decision,
margin of packet origin included HERE => not a caller's complete source
support proof. Through these checks only can transfer dark evaluations to
Pose extension for exact derivatives in Ember at V whenever credentials.
No need success at invalid arguments, but cannot count fallback junk near
queries in continuation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Mirage
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Lattice RG Wilson Pressure Labels Source Extra.Histories
open Warehouse Precision Exterior Tree Carrier Bloch Next.Free Progress.StationaryScenes Bazaars Launch Shapes
open Next.Foundations Vintage Spurs 
open Villa Floor Glints Fizz Fizz.Gush   Cabins  Little Density Little.Core Push.Uniform Honey  Night
open Next.Fluctuations Work.E03 Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {r:ℕ} {n c f : Side} {d : ℕ} {F : Labels.Frame G d}
variable {S:StepData c f}(K:Core G S)(V W:Config G c)

def budget (p:Patch)(R:ℕ) := 4*R+ 20+ predReach p

lemma crosses (s:Signed)(q:Site c) {R} (hc:AgreeNear id (affine s 0 q) (R+1) V W):
     AgreeNear id q R (pull s 0 V) (pull s 0 W) ∧ ∀ a,AgreeNear S.ratio.parent q R (owl K s V a) (owl K s W a) := by
   constructor
   · intro e he; let d:= (posDir e.2).rotate s; let v:=affine s (0:Site c) e.1
     let p:=d.used v
     have h: V p=W p:=by
       apply hc p; change separation _ p.1 ≤ _
       refine (separation_triangle (affine s 0 q) v p.1).trans (Nat.add_le_add (by simp [v,affine]; exact he) ?_); unfold p Step.used; split
       · rw [separation_comm]; have hv := sep_step (v-step d.dir) d.dir; rw [sub_add_cancel] at hv; exact hv
       simp
     unfold pull Lattice.Step.read; split
     · change (V p)⁻¹=(W p)⁻¹; rw [h]
     exact h
   intro a i hi; let p:=sendEdge s 0 i
   have he: upload K V a p=upload K W a p:=by
      unfold upload increment replica; split
      · rfl
      have he:=hc (S.ratio.parent p.1,p.2) ((Mowing.wanders (S:=S) s q i).trans (Nat.add_le_add_right hi _)); rw [he]
   unfold owl pull Lattice.Step.read; split
   · change (upload K V a p)⁻¹=(upload K W a p)⁻¹; rw [he]
   exact he

-- numerical cone: anchored row stencils
private lemma bow_ray (R:ℕ) (i:Twin f) (j:Twin c) : let p:=S.ratio.parent i.1.1; let q:= j.1.1
    (R < separation p q → K.tube.Φ R V i j=0) ∧ (AgreeNear id p R V W → K.tube.Φ R V i j= K.tube.Φ R W i j):= by
    intro p q; constructor
    · intro h; have he(v:Cover): Pressure.casted S K.tube.R R V (mesh i) (mesh j) v=0:=by
        dsimp only [Pressure.casted]; split <;> rename_i H
        · let r := S.ratio.residue (mesh i).1; let w:=route (lift r) (S.patch.L.val • v) 1
          have hb:= sep_walk _ (parent_step S) (mesh i).1 w; rw [show stop _ w=_ from casted_endpoint S (mesh i).1 v,S.ratio.embed_parent,←H.2] at hb
          exact False.elim (h.not_ge (hb.trans H.1))
        rfl
      simp [Tube.Φ,leap,he]
    intro h; apply tsum_congr; intro v; dsimp only [Pressure.casted]; split<;>rename_i H
    · have he : AgreeNear S.ratio.parent p R (replica S.ratio V) (replica S.ratio W):=fun k hk => by
         unfold replica; split
         · rfl
         exact h _ hk
      rw [rated,rated,travel_near _ (parent_step S) _ _ (mesh i).1 _ R H.1 he]
    rfl
private lemma bow_pike (R:ℕ) (i:Bond c) (j:Twin c) : let p:=i.1; let q:=j.1.1
    (R<separation p q → K.tube.Φ' R V i j=0) ∧ (AgreeNear id p R V W→ K.tube.Φ' R V i j=K.tube.Φ' R W i j):=by
   intro p q; let L:= S.patch.L.val
   have hl:1≤L:= S.patch.L.property
   have hz (n:ℕ): n*L ≤ R → n≤R := fun hh=> (le_mul_of_one_le_right (Nat.zero_le _) hl).trans hh
   constructor
   · intro h; have he(v:Cover): Pressure.priced R L V K.tube.R.mn (pole i) (mesh j) v=0:=by
        unfold Pressure.priced; split<;>rename_i H
        · let w:=route 0 v 1; have hc :stop p w=q:=by
            unfold p q; rw [show j.1.1=_ from H.2]; simpa [w,pole] using stop_route i.1 0 v
          have hs := sep_walk (fun x:Site c=>x) sep_step p w; rw [hc] at hs; exact False.elim (h.not_ge (hs.trans (hz _ H.1)))
        rfl
     unfold Tube.Φ' kick lane; simp only [show S.patch.L.val=L from rfl, he,tsum_zero]
   intro h; apply tsum_congr; intro v; unfold Pressure.priced; split
   · rename_i H; rw [rated,rated, travel_near id (fun x k=>sep_step x k) _ _ (pole i).1 _ R (hz _ H.1) h]
   rfl

omit K V W in
lemma crease_eq (K:Core G S) (U U' T T':Config G f) (i:Cell f)(hu:AgreeNear S.ratio.parent (S.ratio.parent i.1) (K.R+4) U U') (ht:AgreeNear S.ratio.parent (S.ratio.parent i.1) (K.R+4) T T') :
    shoot K.tube.high T i=shoot K.tube.high T' i ∧ ∀ j,K.mbTerm U T i j=K.mbTerm U' T' i j:=by
   let L:=S.ratio.parent
   have hq (x:Cell f)(hv:AgreeNear L (L x.1) 4 T T'): faceValue T x = faceValue T' x:= travel_near L (parent_step S) _ _ x.1 (square x.2.val.1 x.2.val.2) 4 le_rfl hv
   refine ⟨?_,fun j=>?_⟩
   · rw [shoot,shoot,hq i (ht.shrink (by unfold L; rw [separation_self]; omega))]
   dsimp only [Little.Core.mbTerm]; split<;>rename_i h; swap; · rfl
   let s:Slot:= (K.tube.up.row i.2 j).2; let p:=Work.F03.slotFace s i.1
   have hh:s.walk.length +4≤ K.R := h
   have hz : travel (expandAt i.1 U) 0 s.walk=travel (expandAt i.1 U') 0 s.walk:= by
     rw [travel_at,travel_at,map_zero,zero_add]; exact travel_near _ (parent_step S) U U' i.1 s.walk _ (by omega) hu
   have hm : p.1=stop i.1 s.walk:=by
     unfold p Work.F03.slotFace Slot.offset; rw [wrap_stop_cover,map_zero,add_comm]; nth_rw 2 [show i.1=i.1+0 by rw [add_zero]]; rw [stop_add_left]
   have hy : faceValue (expandAt i.1 T) (s.offset,s.plaq)=faceValue (expandAt i.1 T') (s.offset,s.plaq):=by
     have he : faceValue T p=faceValue T' p:= hq p (ht.shrink (by rw [hm]; exact Nat.add_le_add ((sep_walk _ (parent_step S) i.1 s.walk).trans (by omega : _≤K.R)) (by omega)))
     unfold faceValue; simp_rw [travel_at]; exact he
   unfold kink; rw [hz,hy]

-- LOCATION transform. Keep Ward g iff agrees absolute K regardless away.
lemma readers (i:Drops c f) (hb:S.patch.Branches S.kernel G) (h:AgreeNear id (shade S i) (budget S.patch K.R) V W):
      garth K i V=garth K i W ∧ ∀ a,logs K i V a=logs K i W a:=by
    let R:=K.R; let η:=predReach S.patch; let r:=S.ratio
    let C:=2*R+8+η
    let s:= i.1; let p:Site c:= i.2.elim (fun i=>r.parent i.1.1) Prod.fst; let z:=affine s 0 p
    have he : z=shade S i:=by
       obtain ⟨s,a|b⟩:=i
       · change affine s 0 (r.parent a.1.1) = r.parent (affine s 0 a.1.1); simp [r,affine,S.ratio.parent_signed S.patch.odd_side]
       rfl
    obtain ⟨hV,hW⟩:= crosses K V W s p (R:=C) (show AgreeNear id z (C+1) V W from he.symm ▸ h.shrink (by unfold budget C; unfold R η; rw [separation_self]; omega))
    let V':=pull s 0 V; let W':=pull s 0 W
    have hy (j:Twin c)(hh:separation p j.1.1≤R) : K.tube.Xn R V' j= K.tube.Xn R W' j:= plotted_near id (fun x k=> sep_step x k) _ _ _ _ R _ j
       S.patch.L.property (hV.shrink (by unfold C; change separation p j.1.1+ (R+4) ≤ _; omega))
    have hp : AgreeNear id p R V' W':= hV.shrink (by unfold C; rw [separation_self]; omega)
    obtain ⟨s',i|i⟩:= i
    · have hc:Twin f:=i; have hw(a) : AgreeNear r.parent (r.parent i.1.1) (R+4) (owl K s V a) (owl K s W a) := (hW a).shrink (by unfold C; change separation p p+_≤_; rw [separation_self]; omega)
      constructor
      · have he' : K.tube.Xf R (owl K s V 0) i=K.tube.Xf R (owl K s W 0) i:= plotted_near _ (parent_step S) _ _ _ _ R 1 _ le_rfl (hw 0)
        change K.tube.Xf R (owl K s V 0) i -_=K.tube.Xf R (owl K s W 0) i -_
        rw [he']; apply congr_arg; apply Finset.sum_congr rfl; intro j _
        have he : K.tube.Φ R V' i j=K.tube.Φ R W' i j := (bow_ray K V' W' R i j).2 hp; rw [he]; by_cases h : separation p j.1.1 ≤R
        · rw [hy _ h]
        rw [(bow_ray K W' V' R i j).1 (Nat.lt_of_not_ge h)]; rfl
      intro a; change crease K s V i a = crease K s W i a
      have hx := crease_eq K _ _ _ _ i.1 (hw 0) (hw a)
      unfold crease; split
      · exact tsum_congr (fun j=> hx.2 j)
      exact hx.1
    have hz(a) :corn K s V a i=corn K s W a i:= prediction_near_eq hb _ _ _ _ ((hW a).shrink (by unfold C; change separation p p+η≤_; rw [separation_self]; omega))
    constructor
    · unfold garth soave; change Tube.Z S _ V' i-_=Tube.Z S _ W' i-_ ; unfold Tube.Z; rw [show V' i= W' i from hV _ (by change separation p p≤_; simp),hz]; apply congr_arg; apply Finset.sum_congr rfl; intro j _
      have he : K.tube.Φ' R V' i j=K.tube.Φ' R W' i j:= (bow_pike K V' W' R i j).2 hp; rw [he]; by_cases h: separation p j.1.1≤R
      · rw [hy _ h]
      rw [(bow_pike K W' V' R i j).1 (Nat.lt_of_not_ge h)]; rfl
    intro a; change gruel K s V i a=gruel K s W i a; unfold gruel; rw [hz,hz]

end YM.Planned.PrimaryIntegral295.Mirage
