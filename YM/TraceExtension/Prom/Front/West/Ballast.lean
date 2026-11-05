import YM.MergeProof.West.Ballast
import YM.TraceExtension.Prom.Front.West.Cabaret
import YM.TraceExtension.Prom.Front.West.Expose
import YM.TraceExtension.Prom.Front.West.Horns
import YM.TraceExtension.Prom.Front.West.Mural
import YM.TraceExtension.Prom.Front.West.Throne
import YM.TraceExtension.Prom.Front.West.View
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Joints
import YM.TraceExtension.Prom.Hill.Memorandum
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Port.Brocade
import YM.TraceExtension.Prom.Port.Soft.Spear
/-!
  Variant of YM.MergeProof.West.Ballast for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open YM.Next.Rank.Tapes.West
open Display Display.Docking
open Function MeasureTheory Lattice Wilson RG Pressure Next.Rank Next.Rank.Perch Tapes
     Spindle Glyph Peak Ac Thirst Corona Value Marker Next.Rank.Station Relation Finset
     Flux RankCovariance Matrix Next.SectorChange Push.SectorMeasure SectorNext.Vacuum
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {i k N p n : ℕ} {ξ : Purse}
    {g : Course C N p k} {B : Binding C} {ht : i<k} {o z : ℝ}
    {P : Rep G (C.S.side (i+1) p)} {R : Rep G (C.S.side i p)}
    (φ : SpearSky B g ξ ht o z P R) (L : Lantern G (C.path.levels.clock.op i p))

local notation "XL" => Atlas.clim C.path.levels i
local notation "XF" => Atlas.clim C.path.levels (i+1)
local notation "BT" => tunnel B N i p
local notation "WX" => ξ.era.coast.Q
local notation "s" => ξ.band
local notation "a" => ξ.horizon
local notation "St" => (C.path.levels.clock.op i p)

set_option quotPrecheck false

variable (X : Points n)
local notation "ID" => (BaleSky C k ξ.band p ξ.horizon X (show i+1≤k from ht))
local notation "ID0" => (BaleSky C k ξ.band p ξ.horizon X (show i≤k from ht.le))
local notation "rd" => (readersSky (C:=C) (b:=ξ.band) (p:=p) X g.allow ((show i≤k from ht.le).trans g.allow))
local notation "rf" => (readersSky (C:=C) (b:=ξ.band) (p:=p) X g.allow ((show i+1≤k from ht).trans g.allow))
local notation "Mar" => ((Ship.yardSky C ξ.band g.allow p).Cell × Fin n)
local notation "TB" => (Fintype.equivFin (Streak (Lantern.park L))).symm
local notation "hf" => 25 * radiusB (retime XL)+30 ≤ R.p.B
variable (W : (BaleSky C k ξ.band p ξ.horizon X (show i+1≤k from ht))→ SourceAt G (readersSky (C:=C) (b:=ξ.band) (p:=p) X g.allow ((show i+1≤k from ht).trans g.allow))) (H : princFtSky C P.p g.allow X ξ.band (show i+1≤k from ht) ξ.era.coast.Q ξ.horizon p W) (hF : Boosted (tunnel B N i p) (tell B i) (retime (Atlas.clim C.path.levels i)))
variable (hb : 25 * radiusB (retime (Atlas.clim C.path.levels i))+30 ≤ R.p.B)

def crestFtSky (j : ID) := rf (j.1,Head j.2.val)
include φ H in
lemma s_light_size_ftSky (j : ID) : (W j).extent=Spindle.patch (WX*walls XF) (crestFtSky (g:=g) (ξ:=ξ) (ht:=ht) X j):= by
  rw [(H j).1,φ.walls]; rfl
include φ

def S_Sunrise_ftSky : (ID ⊕ ID)→ Flake St G (retime XL) L.park rd R.p.threshold := Docking.troupe P R L hF hb (liftHSky (ξ:=ξ) (ht:=ht) X (g:=g)) W XL (crestFtSky (g:=g) (ξ:=ξ) (ht:=ht) X) (WX*walls XF) (s_light_size_ftSky φ X W H)

def s_haloed_ftSky (j : ID) := S_Sunrise_ftSky φ L X W H hF hb (.inl j)
local notation "HL"=> s_haloed_ftSky φ L X W H hF hb
lemma s_fringing_ftSky : F_ringSky s X g.allow ht L WX HL:= by
  refine ⟨fun j=>?_,fun j=>(H j).2⟩
  change wings St R.p.B (W j|>.extent)=_
  rw [φ.budget,(H j).1,φ.walls]

-- p_lanter coefficients view
section
variable (m : C.Makes) (i' : (BaleSky C k ξ.band p ξ.horizon X (show i≤k from ht.le)))
include m
local notation "lit" => litFtSky p g.allow ξ.band C i'.1 i'.2.val
local notation "M" => φ.a_pprove m X L
local notation "Wx" => fun j => (W (i'.1,j)).value
include φ H
omit m in
private lemma s_strobes_ftSky (b : ID) {A : Stores (C.path.levels.clock.op i p)} (k U θ):
    let β:=g.changeβ (i+1)
    (HL b).face A k U θ= InteractingRank.shade A k.wood XL β L.χ (crestFtSky (g:=g) (ξ:=ξ) (ht:=ht) X b) (WX*walls XF) θ • masked P.p.threshold (W b).extent (W b).value (gazed (A:=A) (F:=k.wood) BT k.tag L.χ U (retime XL) β L.hood θ):= by
  intro β; rw [show β=P.beta from φ.fits]; rfl
omit m in
lemma s_consist_ftSky {t} {ετ} {hk : middleSky C.path.levels s k ≤ i} {V : Config G (C.side i p)}
    (q : StageNowSky g (short B N p) X s ht hk WX i' P.p.threshold V ετ) (j : Fin q.count) (θ : (q.tag j).Θ) (ht' : t_ests X s ht (C:=C) i'.2.val t) :
    (q.tag j).Γ t θ • masked P.p.threshold (W (i'.1,t)).extent (W (i'.1,t)).value ((q.tag j).V θ)= p_lantedSky q Wx j t θ:= by
  letI:= (q.tag j).M
  unfold p_lantedSky
  rcases eq_or_lt_of_le (((q.tag j).lives t ht').lower θ) with he | he
  · rw [← he]; simp
  rw [Complex.real_smul,masked_eq _ _ _ _ ?_]; rw [s_light_size_ftSky φ X W H]; exact (q.tag j).field _ ht' _ he
omit H in
lemma s_shaderAt_ftSky (V hV) (j : Fin ((M).tag i' V hV).count) (θ : RoomView (nohole St (retime XL) V) (retime XL) (Streak.wood (TB j)) G) (y : PatchPt X s C.path.levels p a (show i+1≤k from ht)) :
    (((M).tag i' V hV).tag j).Γ y θ= InteractingRank.shade (nohole St (retime XL) V) (Streak.wood (TB j)) XL (g.changeβ (i+1)) L.χ (crestFtSky (g:=g) (ξ:=ξ) (ht:=ht) X (i'.1,y)) (WX*walls XF) θ:= by dsimp only [SpearSky.a_pprove, e_xposeSky]; rfl
omit H in
lemma s_gazerAt_ftSky (V hV) (j : Fin ((M).tag i' V hV).count) (θ : RoomView (nohole St (retime XL) V) (retime XL) (Streak.wood (TB j)) G) :
    (((M).tag i' V hV).tag j).V θ= gazed (A:=nohole St (retime XL) V) (F:=(Streak.wood (TB j))) BT (Streak.tag (TB j)) L.χ V (retime XL) (g.changeβ (i+1)) L.hood θ := by dsimp only [SpearSky.a_pprove, e_xposeSky]
lemma s_foliated_ftSky (V hV) (j : Fin ((M).tag i' V hV).count) (θ : (((M).tag i' V hV).tag j).Θ)
    (y : PatchPt X s C.path.levels p a (show i+1≤k from ht)) (ht' : t_ests X s ht (C:=C) i'.2.val y):
    (HL (i'.1,y)).face (nohole St (retime XL) V) (TB j) V θ=p_lantedSky ((M).tag i' V hV) Wx j y θ := by
  let y':ID:=(i'.1,y)
  refine (Eq.trans (s_strobes_ftSky φ L X W H hF hb y' (A:=nohole St (retime XL) V) (TB j : Streak L.park) V θ) (Eq.trans ?_ (s_consist_ftSky φ X W H i' ((M).tag i' V hV) j θ ht')))
  exact congr_arg₂ (fun (v:ℝ) (X : Config G (C.side (i+1) p)) => v • masked P.p.threshold (W y').extent (W y').value X) (s_shaderAt_ftSky φ L X m i' V hV j θ y).symm (s_gazerAt_ftSky φ L X m i' V hV j θ).symm

set_option maxHeartbeats 400000 in
lemma s_bookends_ftSky (V hV) (j : Fin ((M).tag i' V hV).count) (θ : (((M).tag i' V hV).tag j).Θ) :
    let S:= TB j
    pages HL (lit).val (nohole St (retime XL) V) S V θ = bed (lit).val (insertAt i'.1 (Poly.pass (p_lanterSky ((M).tag i' V hV) Wx j θ))):= by
  intro k'
  let Q:= (M).tag i' V hV; let D:=Q.tag j; let A:=(lit).val
  let U:= V; let f:= D.V θ
  let R':= flakeTone ∘ HL
  let Y (i:ID) : veil (CellPSky C k ξ.band p × Fin n):= ingrain R' i (nohole St (retime XL) V) k' V θ
  have hk i: (Y i).part (quiet Mar)=0:= Flux.asleep _ (W i).chosen _
  have hb' P: bed A (Poly.pass (P : veil (CellPSky C k ξ.band p × Fin n)))=Poly.pass ((bed A) P) := by -- PASS always same counts, no hv
    unfold Poly.pass; rw [map_sum]; exact Finset.sum_congr rfl fun i _=> (map_smul ..).trans (congr_arg _ (map_pow ..))
  have ht' (y : PatchPt X s C.path.levels p a (show i+1≤k from ht)) :
      bed A (Y (i'.1,y)) = bed A (insertAt i'.1 (if t_ests X s ht (C:=C) i'.2.val y then Poly.send (tag y.val).val (p_lantedSky Q Wx j y θ) else 0)):= by
    let t : ID:= (i'.1,y)
    have hq : (W t).fires.val⊆ A ↔ Tapes.West.t_ests X s ht (C:=C) i'.2.val y:= by rw [(H t).2]; exact (roiSky s X g.allow ht t i').trans ⟨And.right,fun h=>⟨rfl,h⟩⟩
    split
    next hY=>
      apply congr_arg; rw [insert_send]; change Poly.send (W t|>.fires) _= _
      rw [(H t).2]; refine congr_arg _ ?_
      exact s_foliated_ftSky φ L X W H hF hb m i' V hV j θ y hY
    next he=>
      simp only [map_zero]; change bed A (Poly.send (W t|>.fires) _)=0
      rw [shelved,if_neg]; exact mt hq.mp he
  let K:=PatchPt X s C.path.levels p a (show i+1≤k from ht)
  change bed A (∏ i,(Y i+1))=_
  rw [show (∏ i,(Y i+1))=Poly.pass (∑ i,Y i) by rw [Exponential.pass_sum]; exact Finset.prod_congr rfl fun i _ => (Flux.solo _ _ (W i).chosen).symm; exact fun i _=> hk _, ← Glyph.insert_pass _ _ (un_quietSky ..),hb',hb']; apply congr_arg Poly.pass
  change bed A (∑ i,Y i)= bed A (insertAt i'.1 (p_lanterSky Q Wx j θ))
  rw [Fintype.sum_prod_type,map_sum,Finset.sum_eq_single i'.1]
  · unfold p_lanterSky; rw [map_sum, map_sum,map_sum]; exact Finset.sum_congr rfl fun i _=>ht' i
  · intro y _ he; rw [map_sum]; apply Finset.sum_eq_zero; intro w _
    change bed A (Poly.send (W _|>.fires) _) =0
    rw [shelved, (H (y,w)).2, if_neg]
    intro Hz; exact he ((roiSky s X g.allow ht (y,w) i').1 Hz).1
  simp

omit m φ H in
private def s_particip_ftSky {U : Type*} [Fintype U] [DecidableEq U] (z : modes U) : veil U →L[ℝ] ℂ:= LinearMap.toContinuousLinearMap ({
    toFun:= (fun i:veil U=>i.part z)
    map_add':=fun a' b=>Poly.part_plus ..
    map_smul':=fun v b=>by simp only [RingHom.id_apply,← Complex.coe_smul v b, ← Complex.coe_smul v (b.part z),Poly.part_smul,smul_eq_mul]
    } : veil U→ₗ[ℝ] ℂ)

omit m φ H in
private lemma s_focused_ftSky {X Z Y : Type} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq Z] [Fintype Y] {U : Y→Type} [∀ y,MeasurableSpace (U y)] (p : X) (Q : Finset (X× Z)) (f : ∀ y : Y,U y → veil (X×Z)) (g : ∀ y : Y,U y→veil Z)
    (μ : ∀ y : Y,Measure (U y)) (w : Y→ℝ) (h : ∀ y,Integrable (f y) (μ y)) (hh : ∀ y i,f y i= Flux.bed Q (insertAt p (g y i))) :
    ∑ i,w i • ∫ x,f i x∂μ i=Flux.bed Q (insertAt p (Poly.inject fun v=>∑ i,(w i:ℂ)*∫ u,(g i u).part v∂μ i)):= by
  ext i; rw [Poly.part_sum,Flux.shelve,insert_part]; let F:=s_particip_ftSky i
  have he j : (w j • ∫ x, f j x∂ μ j).part i= (w j:ℂ)* ∫ u,(Flux.bed Q (insertAt p (g j u))).part i∂μ j:= by
    change F (w j • ∫ x, f j x∂ μ j)=_; rw [map_smul,← F.integral_comp_comm (h j), Complex.real_smul]; apply congr_arg; exact integral_congr_ae (Filter.Eventually.of_forall fun x=>congr_arg F (hh j x))
  split_ifs with hp ht
  · apply Finset.sum_congr rfl; intro j _;rw [he];simp_rw [Flux.shelve, if_pos hp,insert_part,if_pos ht]
  · apply Finset.sum_eq_zero;intro j _; rw [he]; simp only [Flux.shelve,if_pos hp,insert_part, if_neg ht,integral_zero,mul_zero]
  apply Finset.sum_eq_zero; intro j _; rw [he]; simp only [ Flux.shelve,if_neg hp,integral_zero,mul_zero]

lemma s_foreword_ftSky (U hU) (hp : Ticketed HL (lit).val BT U) : Flux.bed (lit).val (Flux.chair (zone (flakeTone ∘ HL)) (fun i=>proceeds (flakeTone∘ HL) BT i U) univ)= Flux.bed (lit).val (insertAt i'.1 (planterFtSky ((M).tag i' U hU) Wx)) := by
  let Q:= (M).tag i' U hU; let X':= TB; let I:= nohole St (retime XL) U; let f j:= pages HL (lit).val I j U; let μ (j:Streak L.park):= viewer BT I (retime XL) j.wood j.tag U
  obtain ⟨he,h⟩:= impression HL (lit).val hF U hp
  have hz := s_bookends_ftSky φ L X W H hF hb m i' U hU
  refine h.symm.trans ?_; unfold glance
  rw [← Equiv.sum_comp X']
  let r (i : Fin Q.count) (u : (Q.tag i).Θ) := Poly.pass (p_lanterSky Q Wx i u)
  letI (i : Fin (Fintype.card (Streak L.park))) : MeasurableSpace (RoomView I (retime XL) (X' i).wood G):= inferInstance
  exact s_focused_ftSky (U:=fun i:Fin Q.count=>RoomView I (retime XL) (X' i).wood G) i'.1 (lit).val (fun i=>f (X' i)) (fun i y=>r i y) (fun i=> μ (X' i)) (fun i=>Streak.share (X' i)) (fun i=>he _) hz
end
end YM.PhysicalNext.InteractingRank.Soft
