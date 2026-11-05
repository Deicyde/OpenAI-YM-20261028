import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Slate
import YM.Push.LOCAL_SPLITTING.Marginal


/-! # First system values on the *actual* charts: after assembly

Out of camera data: `letter` on one new club. `projected_club`: exact
product at reweighted density terms, keeping all data on actual A and
markers. No integrability claimed on unions of overlaps from just
integrability on individual vertices which can overlap (buy that later).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display
open Lattice Wilson Pressure RG Filter MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid SectorNext.Vacuum Precision
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}
    {x τ : ℝ} {F : Orchard S} {T : Tube G S} {A : Stores S}
    {P : Teller G} {k : Streak F} {V : Config G c}
    {W ι : Type} [Fintype W] [DecidableEq W] {u : W → Site c} (Q : ι→ PaintCan S G x F u τ) (ht : Boosted T P x)

def letter (i : Club Q) := glance T (stage Q i.val) (glow Q i.val)
def proceeds (T : Tube G S) (i : Club Q) (V : Config G c) := if validArea Q i V then Poly.send (fires Q i.val) (letter Q (T:=T) i V) else 0

section pass
variable [DecidableEq ι]

def ingrain (i : ι) : Shader G S x F (Glyph.veil W) := fun A k U z=> Poly.send (Q i).hues ((Q i).lamp A k U z)

def risen (s : Finset ι) : Shader G S x F (Glyph.veil W) := fun A k U z=> ∏ i∈s,ingrain Q i A k U z

private lemma stamp_vector (F : Finset ι) (B : ι → ℂ) (c : ι→ modes W) (H : (F:Set _).PairwiseDisjoint (fun i=> (c i).val)) :
    (∏ i∈F,Poly.send (c i) (B i)) = Poly.send (scene (F.biUnion (fun i=> (c i).val))) (∏ i∈F,B i):= by
  induction F using Finset.induction_on with
  | empty=>rw [biUnion_empty,prod_empty,prod_empty];rfl
  | insert i s hi ih =>
    have hm : (s:Set _).PairwiseDisjoint (fun i=> (c i).val):= fun i hi j hj h=> H (mem_insert_of_mem hi) (mem_insert_of_mem hj) h
    rw [prod_insert hi,prod_insert hi,ih hm,plate_pair,if_pos,biUnion_insert]; rfl
    apply Finset.disjoint_left.mpr; intro x hx hj; obtain ⟨j,hj,hp⟩:=mem_biUnion.mp hj; exact Finset.disjoint_left.mp (H (mem_insert_self ..) (mem_insert_of_mem hj) (ne_of_mem_of_not_mem hj hi).symm) hx hp
lemma rising (s : Finset ι) (h : enlist Q s) (U : Config G c) (k:Streak F) (z : RoomView A x k.wood G):
    risen Q s A k U z=Poly.send (fires Q s) (stage Q s A k U z):=stamp_vector s (fun i=>(Q i).lamp A k U z) _ h.2
lemma no_clash (s : Finset ι) (h : ¬(s:Set _).PairwiseDisjoint (fun i=>(Q i).hues.val)) (U : Config G c) (k:Streak F) (z : RoomView A x k.wood G) :
    risen Q s A k U z=0:=by
  unfold Set.PairwiseDisjoint Set.Pairwise at h; push Not at h
  obtain ⟨i,hi,j,hj,hh,h⟩:=h; change i∈s at hi; change j∈s at hj
  have he : ingrain Q i A k U z*ingrain Q j A k U z=0:= (plate_pair ..).trans (if_neg h)
  unfold risen; rw [←mul_prod_erase _ _ hi,← mul_prod_erase _ _ (show j∈ s.erase i from Finset.mem_erase.mpr ⟨hh.symm,hj⟩), ← mul_assoc,he,zero_mul]
omit [DecidableEq ι] in
lemma billed_flux (s : Finset ι) (h : enlist Q s) (r : W→ℝ) : Poly.toll r (fires Q s) = ∏ i∈s,Poly.toll r (Q i).hues:= Finset.prod_biUnion h.2
lemma party_marks (s : Finset (Club Q)) (hp : (s:Set _).PairwiseDisjoint (zone Q)) (B : Club Q → ℂ) :
    ∏ i∈s,Poly.send (fires Q i.val) (B i) = Poly.send (fires Q (draw Q s)) (∏ i∈s,B i):= by
  rw [stamp_vector _ B _ ?_]; congr 1
  · apply congr_arg scene; unfold draw; ext; simp [fires,scene]; grind
  intro i hi j hj hh; refine Finset.disjoint_left.mpr fun t ht hv=> Finset.disjoint_left.mp (hp hi hj hh) (knows Q _ _ ht) (knows Q _ _ hv)
private def sendL (u : modes W) : ℂ →L[ℝ] veil W := LinearMap.toContinuousLinearMap ({
    toFun:= Poly.send u
    map_add':=fun i j=> by ext; simp [Poly.part_send]; split<;>simp
    map_smul':= fun z x=> by simp only [RingHom.id_apply];rw [← Complex.coe_smul z x,← Complex.coe_smul z (_:veil W)]; ext; simp only [Poly.part_send,Poly.part_smul,smul_eq_mul]; split<;>simp
    } : ℂ →ₗ[ℝ] veil W)
-- all integrals before cluster reindex use authorization from same run
-- Λ need not be globally integrable here (pointwise certificate).
include ht in
lemma inspected (s : Finset ι) (h : enlist Q s) (V : Config G c) (p : Finset (Club Q))
    (hp : (p : Set _).PairwiseDisjoint (zone Q)) (H : draw Q p=s) (hx : ∀ i∈p,validArea Q i V)
    (hb : ∀ i∈p, ∀ k : Streak F, Integrable (stage Q i.val (stapled x (glow Q i.val) V) k V) (viewer T (stapled x (glow Q i.val) V) x k.wood k.tag V)) :
    let A:=stapled x (glow Q s) V
    (∀ k, Integrable (risen Q s A k V) (viewer T A x k.wood k.tag V)) ∧
      glance T (risen Q s) (glow Q s) V=∏ i∈p, proceeds Q T i V := by
  intro A
  let σ:= stage Q s; let L:=glow Q s
  let v (i: Club Q) (k:Streak F):= ∫ y,stage Q i.val A k V y∂viewer T A x k.wood k.tag V
  have hc i (hi:i∈p) k: let q : Club Q:=i; let B:= glow Q i.val; let C:=stapled x B V
                          Integrable (stage Q i.val A k V) (viewer T A x k.wood k.tag V) ∧
                            v i k=(∫ y,stage Q i.val C k V y∂viewer T C x k.wood k.tag V):= by
    intro q B C
    have hz := integrate_beam (observer Q i) ht (position ..) (position ..) (windings Q p i hi hp V k) (fun _=>rfl)
    rw [H] at hz; exact ⟨hz.1.mp (hb i hi k), hz.2.symm⟩
  have he :stage Q s=(fun A k U z=> ∏ i∈p,stage Q i.val A k U z):= by
    funext A k V z; unfold stage; rw [← H,draw,prod_biUnion (autonomy Q hp)]
  obtain ⟨hI,hJ⟩:= inter_spec p (zone Q) (fun i=>stage Q i.val) ht (fun i _=>observer Q i) hp (A:=A) (L:=L) rfl (fun i hi k=> (hc i hi k).1)
  have hQ k:Integrable (stage Q s A k V) (viewer T A x k.wood k.tag V):= by rw [he];exact hI k
  have h₂ : glance T (stage Q s) L V= ∏ i ∈ p,letter Q (T:=T) i V := by
    rw [he,hJ]; exact Finset.prod_congr rfl fun i hi=> Finset.sum_congr rfl fun k _=>congr_arg _ (hc i hi k).2
  have hs : risen Q s= fun A k U z=> sendL (fires Q s) (stage Q s A k U z):= funext fun A=>funext fun k=>funext fun U=>funext fun z=> rising Q s h U k z
  rw [hs]; let E:=sendL (fires Q s)
  refine ⟨fun k=> E.integrable_comp (hQ k),?_⟩
  calc
    _ = E (glance T (stage Q s) L V) := by
      unfold glance; rw [map_sum]; apply Finset.sum_congr rfl; intro k _
      change _=E (_• ∫ y,stage Q s A k V y∂_); rw [map_smul]; exact congr_arg ((Streak.share k) • ·) (E.integral_comp_comm (hQ k))
    _ = ∏ i∈p, Poly.send (fires Q i.val) (letter Q (T:=T) i V) := by rw [party_marks _ _ hp,H,h₂]; rfl
    _ = _ := Finset.prod_congr rfl fun i hi=> (if_pos (hx i hi)).symm
include ht in
lemma projected_club (s : Finset ι) (h : enlist Q s) (V : Config G c) (hx : cardGoal Q s= flags τ V) (p : Finset (Club Q))
    (hp : (p : Set _).PairwiseDisjoint (zone Q)) (H : draw Q p=s)
    (hb : ∀ i∈p, ∀ k : Streak F, Integrable (stage Q i.val (stapled x (glow Q i.val) V) k V) (viewer T (stapled x (glow Q i.val) V) x k.wood k.tag V)) :
    let A:=stapled x (glow Q s) V
    (∀ k, Integrable (risen Q s A k V) (viewer T A x k.wood k.tag V)) ∧
      glance T (risen Q s) (glow Q s) V=∏ i∈p, proceeds Q T i V := inspected Q ht s h V p hp H (zone_pass Q hp (by rw [H];exact hx)|>fun h=>h) hb
end pass
end YM.PhysicalNext.InteractingRank.Display
