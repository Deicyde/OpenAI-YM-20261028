import YM.MergeProof.West.Laurel
import YM.TraceExtension.Prom.Front.West.Cedar
import YM.TraceExtension.Prom.Front.West.Dink
import YM.TraceExtension.Prom.Front.West.Jenn
import YM.TraceExtension.Prom.Front.West.Knight
import YM.TraceExtension.Prom.Front.West.Liza
import YM.TraceExtension.Prom.Front.West.Mallow
import YM.TraceExtension.Prom.Front.West.View
import YM.TraceExtension.Prom.Front.West.Vroom
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Gust
import YM.TraceExtension.Prom.Hill.Joints
import YM.TraceExtension.Prom.Hill.Memorandum
import YM.TraceExtension.Prom.Hill.Station
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open MeasureTheory Cells Edition Filter
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge}{N n p k q i l j d D m u:ℕ} {C:Family G}{x:Points m} {ξ:Purse} {R:Lead G C.S p} {c:Course C N p k}{P:(i:ℕ)→ Rep G (C.side i p)}{s:ℝ}{Ψ:AtlasData G C.S p}
section
variable {n : Side} {V ι κ : Type} [Fintype V] [DecidableEq V]
private lemma basicLightSky {ζ : V→ Site n} [Fintype ι] [Fintype κ] {r R : V→ℝ} {h k e₀ : ℝ} (L : Rep G n) {A : ι→ SourceAt G ζ} {K : κ→ Lifted G ζ L.p.threshold} (H : Unpacks A L.p r e₀ h) (ht : prepared (q:=L.p) K r e₀ k) (hp : ∀ i,0≤ R i) (hr : R ≤ r): Light L A K R e₀ h k:= by
  have ht' (s:modes V): Poly.toll R s ≤ Poly.toll r s:= Finset.prod_le_prod (fun i _=> hp i) (fun i _=> hr i)
  obtain ⟨m,hm,h⟩:=H; obtain ⟨p,hp,hk⟩:=ht; constructor
  · refine ⟨fun i=>m i*Value.charge L.p e₀ (A i).extent, fun i=>⟨mul_nonneg (hm i|>.1) (Real.exp_pos _).le,fun U hx=>?_⟩, fun i=>?_⟩
    · refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ht' _) (Real.exp_pos _).le) (norm_nonneg _)) ?_; rw [mul_assoc]; apply (mul_le_mul_of_nonneg_left (((transferD ..).mp (hm i)).2 _ hx) (Real.exp_pos _).le).trans_eq (mul_comm ..)
    simpa [Value.charge] using! (sum_pay _ _ _ (fun i=>mul_nonneg (hm i|>.1) (Real.exp_pos _).le)).1 (h i)
  refine ⟨fun i=>p i*Value.charge L.p e₀ (K i).extent, fun i=>⟨mul_nonneg (hp i|>.1) (Real.exp_pos _).le,fun U=>?_⟩,fun i=>?_⟩
  · refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ht' _) (Real.exp_pos _).le) (norm_nonneg _)) ?_; rw [mul_assoc]; exact (mul_le_mul_of_nonneg_left ((hp i).2 U) (Real.exp_pos _).le).trans_eq (mul_comm ..)
  simpa [Value.charge] using! (sum_pay _ _ _ (fun i=> mul_nonneg (hp i|>.1) (Real.exp_pos _).le)).1 (hk i)

end
variable {d : Fin (m+1) → ℕ} (x:Points (m+1))(v:(i:Fin (m+1))→ C.label (d i))
   (F:(i:Fin (m+1))→ StampDuty C k N p (d i) ξ.taylor (P k) ξ.era.coast.Q Ψ)

local notation "AX" => C.path.levels
local notation "B" => ξ.band
local notation "T" => Ship.yardSky C ξ.band c.allow p
local notation "Y" => (fun i => prefaced (F i) (v i) (Station.choose AX B k x i))

set_option quotPrecheck false
variable (Xg:CeremonySky ξ c P R Ψ) (hv:Kith (A:=C.path.levels) (fun i:Fin (m+1)=> prefaced (F i) (v i) (Station.choose C.path.levels ξ.band k x i)) x ξ)
    (hq:Caff (G:=G) ξ (clim C.path.levels k) (k-middleSky C.path.levels ξ.band k) u (m+1))
include Xg
local notation "λ1" => (readyHXSky m (scouts C k) x ξ.band c.allow v (fun i=> (F i).coupon (v i)))
local notation "τ"=>clim C.path.levels k
local notation "r"=> ξ.cash τ
lemma staunchSky (hu:2 ≤ u)
    (h:RodXSky m x ξ.band c.allow v c (P k) λ1 (load ξ.era) r (bill (-(ξ.goal:ℝ)) τ) (Real.exp (-Paint.trib ξ.era.coast.a τ))): leasedSky Xg hv hq le_rfl (beforeSky AX ξ.band k) (IssuedXSky C ξ.band x c.allow p v):=by
  obtain ⟨ι,κ,ha,hb,H,K,hL,hB,hT,hw⟩:= h
  let W:= tapestrySky hv hq le_rfl (beforeSky AX ξ.band k) Xg.sens c
  let α:= ListensSky C ξ.band (v:=m+1) c.allow p; let β:=BaleSky C k ξ.band p ξ.horizon x le_rfl; let V:α→ _ := λ1
  let G' : α → β:= fun t=> ⟨t.1,solitaire x t.2 ξ p k AX⟩
  have hQ: (P k).p.B=walls τ:= (Xg.birth k (beforeSky ..) le_rfl).1
  unfold leasedSky; dsimp only
  refine ⟨ι,κ,ha,hb,H,K,hL.trans ?_,hB,?_⟩
  rotate_left
  · rw [Nat.sub_self,Purse.epoch,pow_zero,one_mul]; rw [show gas ξ.era.coast τ=Real.exp (-Paint.trib ξ.era.coast.a τ) by unfold Perch.gas Paint.trib; ring_nf]
    exact basicLightSky (P k) hT hw (fun i=> (Real.exp_pos _).le) (fun i=> Glimmer.billed _ (cash_le _ _ hu))
  ext1 U; unfold dust; rw [Fintype.sum_sum_type,Fintype.sum_sum_type]; congr 3
  let b:= (P k).p.threshold; let q:= ξ.era.coast.Q
  have he (t : α):(W (G' t)).amount b U=(V t).amount b U:= by
    let z:= (solitaire x t.2 ξ p k AX).val
    have hx : (W (G' t)).extent=(V t).extent:= by
      change Spindle.patch (q*walls τ) (readersSky (C:=C) (b:=ξ.band) x c.allow c.allow (t.1,Head z))=swath (handSky C B c.allow p t) (seatsSky C B x c.allow p t) (halo (q*(P k).p.B) {0}); rw [swath_iffHalo,x_head x t.2 (C:=C),hQ]; simp only [swath,image_singleton,affine,Signed.act_zero,zero_add]; rfl
    have ht:(W (G' t)).fires=(V t).fires:= by
      apply Subtype.ext; change {t.1} ×ˢ ({t.2}: Finset _)={t}; rw [singleton_product_singleton]
    have hh:(W (G' t)).value=(V t).value:=by
      funext u; change gloryFtSky (C:=C) x B p c.allow le_rfl (beforeSky ..) t.1 z (anneals C c k) (vista R Y le_rfl z.val) u=_; rw [bootwarm C c c.allow]; exact x_journeySky x v F Xg t.1 t.2 _ _
    rw [SourceAt.amount,SourceAt.amount,hx,ht,hh]
  apply congr_arg ((∑ i,(H i).amount b U)+·)
  change (∑ i,(V i).amount b U) = ∑ i,(W i).amount b U
  let X:=(univ (α:=α)).image G'
  have ht : Injective G':=fun i j h=> by
    refine Prod.ext (show (G' i).1=(G' j).1 from congr_arg Prod.fst h) ?_
    exact Finset.singleton_injective (congr_arg (fun x:β=> x.2.val.val.val) h)
  rw [← sum_subset (subset_univ X) ?_,sum_image ht.injOn]; simp_rw [he]
  intro i _ hh
  let Q:=i.2.val.val
  have hx:2 ≤ Q.val.card:=by
     have hp: (0:ℕ)<Q.val.card:= Finset.card_pos.mpr i.2.val.property; by_contra! hz; obtain ⟨x',hx'⟩:=Finset.card_eq_one.mp (show Q.val.card=1 by omega)
     have he:G' (i.1,x')=i:= Prod.ext rfl (Subtype.ext (Subtype.ext (Subtype.ext (hx'.symm))))
     exact hh (mem_image.mpr ⟨_,mem_univ _,he⟩)
  change Poly.send (W i).fires (masked b (W i).extent (W i).value U) = _
  by_cases hz: Healthy b (W i).extent U
  · rw [masked_eq b _ _ _ hz]
    have hx:vista R Y le_rfl Q=0:= strophe (C:=C) Y Q hx
    unfold Q at hx
    simp only [W,tapestrySky,mimicFtSky,gloryFtSky,hx,caseW,Function.comp_apply,text,map_zero,Edition.dot_zero,Poly.send_zero]
  rw [masked_ne _ _ _ _ hz,Poly.send_zero]
end YM.Next.Rank.Tapes.West
