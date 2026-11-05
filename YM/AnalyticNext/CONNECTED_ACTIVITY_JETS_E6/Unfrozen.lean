import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Erosion
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Polar

/-!
# Manifest-independent unmasked local columns. Neither side paid a Budget prior.

 Use even for eventual sampling near support ONLY using flags on original
 field. Same stuffed data at chosen Ω.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open Pulse Itinerary Raw Matter Blaze.Scroll Blaze.Vine Blaze.Polar Blaze.Frond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {x : Site c} {X X' : Coat T F} {a b : ℕ}
namespace Zone
variable (H : Zone X X' x a) (p : Room P S T X.x)

include p H
lemma needle (s : Signed) (i : Rod c f) (he : x=s.act (focus S i)) (hs : 12*X.B≤a) (u u' : Directions G f)
    (hp : ∀ j,distAt S j x ≤ X.B → X.Hot j → u j=u' j) : strain X s i u=strain X' s i u' := by
  let o:= focus S i; let V:=pull s 0 X.V; let V':=pull s 0 X'.V
  have hv : 100≤X.B := p.sight.1
  have hb := H.real p s i he hs u u' hp
  have h : AgreeNear id o (radiusB X.x/4) V V' := Zone.nearV s (H.pay.shrink (by rw [he]; change separation (s.act o) (s.act o)+(X.B/4+1)≤_; rw [separation_self]; omega))
  have hx := LocalRows.costsX p i h
  have hF := shoreVisa p i h
  let Y (X : Coat T F) := pull s 0 X.V
  have hP (X : Coat T F) u : strain X s i u=X.realPath s i u+guide T X.x (Y X) i - visual T (till X.x) (Y X) i := by
    unfold strain Coat.realPath request freely Y; abel
  rw [hP,hP,hb,← H.temp,show guide T X.x (Y X) i=guide T X.x (Y X') i from hx,
    show visual T (till X.x) (Y X) i=visual T (till X.x) (Y X') i from hF]

lemma spindle (q : Tubular f G) (hq : x=along S q) (h : 13*X.B≤a) : leanB X q=leanB X' q := by
  unfold leanB Matrix.mulVec dotProduct; refine sum_congr rfl fun i hi=> ?_
  simp only [Matrix.transpose_apply,stand]
  by_cases ht : separation x (aim S i) ≤ X.B/4
  · have he:= H.tune_down (q:=aim S i) (b:=12*X.B) (by omega)
    have hv: aim S i=X.addr i.1.1 (spot S i.1.2) := by unfold Coat.addr; rw [← cost_is_here]; rfl
    rw [(H.coupling p q hq h i).1 ht]; unfold Blaze.Vine.bar; rw [he.shifting _ _ hv (by omega), he.needle p i.1.1 i.1.2 rfl le_rfl 0 0 (fun _ _ _=>rfl)]
  obtain ⟨hx,hq⟩:= (H.coupling p q hq h i).2 ht; rw [hx,hq,zero_mul,zero_mul]
lemma spirals (q : Tubular f G) (he : x=along S q) (ha : 17*X.B ≤ a) : well X q=well X' q := by
  unfold well; rw [Pi.neg_apply,Pi.neg_apply]; apply congr_arg Neg.neg
  unfold Matrix.mulVec dotProduct; refine sum_congr rfl fun i _=> ?_; dsimp only; rw [Matrix.transpose_apply,Matrix.transpose_apply,← H.changeL p q he i (by omega)]
  by_cases hi : separation x (along S i) ≤ X.B+2
  · have hF : 100≤X.B := p.sight.1
    rw [(H.tune_down (q:=along S i) (b:=13*X.B) (by omega)).spindle p i rfl le_rfl]
  rw [he,separation_comm] at hi; rw [kernelA,X.shutter.thin _ i q (lt_of_not_ge hi),zero_mul,zero_mul]

lemma shinesP (q : Tubular f G) (he : x=along S q) (ha : 18*X.B ≤ a) (v : ℝ) : shimmer X v q=shimmer X' v q := by
  unfold shimmer; rw [Pi.smul_apply,Pi.add_apply,Pi.smul_apply,Pi.add_apply, H.spindle p q he (by omega)]
  unfold Matrix.mulVec dotProduct; dsimp only
  suffices h : (∑ i, X.plate q i * well X i)=(∑ i,X'.plate q i * well X' i) by rw [h]
  refine sum_congr rfl (fun i _=>?_)
  by_cases hg : separation x (along S i) ≤ X.B/2
  · have hv := H.tune_down (q:=along S i) (b:=17*X.B) (by omega); rw [H.plateL p q he (by omega), hv.spirals p i rfl le_rfl]
  rw [he] at hg; rw [X.span p q i (lt_of_not_ge hg),X'.span (H.temp ▸ p) q i (by rw [H.B]; exact lt_of_not_ge hg),zero_mul,zero_mul]
end Zone

variable {k k' : Finset ℕ} {R : Rep G f} {Z : Support c} {w v : Air f G}
namespace Coat
variable (X : Coat T F)
def reform (β : ℝ) (u : Directions G f) := WithLp.toLp 2 (stand ((gStep β)⁻¹ • (u-X.μ)))
lemma oldysis {β : ℝ} (h : 0<β) (u : Directions G f) : X.liftA β (X.reform β u)=u := by
  unfold liftA
  have hg := inv_pos.mpr (Real.sqrt_pos.mpr h)
  rw [show X.atmos (X.reform β u)=(gStep β)⁻¹ • (u-X.μ) from rfl, smul_inv_smul₀ (show gStep β ≠ 0 from hg.ne')]
  abel
end Coat
namespace Borough
variable (H : Borough X X' Z w v k k' R) (p : Room P S T X.x)
include p H
lemma hair (i : Bond f) (he : Cleanroom Z (25*X.B) (atEdge S i)) (β : ℝ) : voltage X i=voltage X' i ∧
    worldZ X β w i=worldZ X' β v i := by
  have hx := H.social (x:=atEdge S i) (a:=17*X.B) (fun i hi=>he i (by have hv:100≤X.B:=p.sight.1; omega))
  have hh : voltage X i=voltage X' i := by ext j; exact hx.spirals p (i,j) rfl le_rfl
  refine ⟨hh,?_⟩; unfold worldZ; rw [Pi.add_apply,Pi.add_apply,Pi.smul_apply,Pi.smul_apply,hh,(H.lodge p he).2]
lemma rooms (β : ℝ) : Borough X X' Z (X.reform β (worldZ X β w)) (X'.reform β (worldZ X' β v)) k k' R := by
  refine ⟨H.toVillage,fun i hi=>?_,H.covering⟩; have hh : Cleanroom Z (25*X.B) (atEdge S i.1) := (mem_filter.mp hi).2
  unfold reform; unfold stand
  simp only [Pi.smul_apply,Pi.sub_apply,(H.hair p _ hh β).2,(H.lodge p hh).1]

-- Reading in old coordinates available. use on angular Δ etc.
lemma cornice (s : Stream c f) (he : Cleanroom Z (30*X.B) (rowSite S s)) :
    let u:=X.liftA R.beta w; let u':=X'.liftA R.beta v
    Blaze.Vine.costs X (voltage X) s.1 s.2 = Blaze.Vine.costs X' (voltage X') s.1 s.2 ∧
    ∀ i, rootface X u (X.input u) i s.1 s.2 = rootface X' u' (X'.input u') i s.1 s.2 := by
  intro u u'; rcases s with ⟨s,i⟩; let o:=lead S i; let t:= s.act o
  have hh : 100 ≤ X.B := p.sight.1
  have hS : Zone X X' t (20*X.B) := H.social (x:=t) (fun j hj=> he j (by change separation t j≤_; omega))
  have hc (g b : Directions G f) (ht : ∀ j : Bond f, distAt S j t≤ X.B → X.Hot j → g j=b j) :
      Blaze.Vine.costs X g s i=Blaze.Vine.costs X' b s i := by
    unfold Blaze.Vine.costs; apply sum_congr rfl; intro j hj; have hk := (parent_iff (S:=S) j i).1 hj
    have hy := hS.needle p s j (by unfold t o; rw [cost_is_here j,hk]) (by omega) g b ht
    unfold Blaze.Vine.pot; rw [hk,hS.shifting s i rfl (by omega),hy]
  have hz (i : Bond f) (hi : distAt S i t ≤ X.B) : Cleanroom Z (25*X.B) (atEdge S i) := by
    apply fans he; unfold distAt at hi; change separation t _+_ ≤_; omega
  refine ⟨hc _ _ (fun j hj _=> (H.hair p j (hz j hj) R.beta).1), fun b=>?_⟩
  have hT := funds_branch p.accepted
  let U:= X.input u; let U':= X'.input u'
  dsimp only; unfold rootface; rw [← H.weather,hc u u' (fun j hj _=> H.house p (hz j hj) _)]
  apply congr_arg₂ (·-·) _ rfl
  have hv : AgreeNear id o (X.B/2) (pull s 0 X.V) (pull s 0 X'.V) := Zone.nearV s (hS.pay.shrink
    (by change separation t t + (X.B/2+1) ≤_; rw [separation_self]; omega))
  apply Blaze.Frond.rivers p i (choice s X.k) (choice s X'.k) hv
  · apply Zone.nearU S s ((H.intake p he).shrink (q':=t) (by change separation t t+(X.B/2+1) ≤_; rw [separation_self]; omega))
  rw [(carry s hT X.k U).2,(carry s hT X'.k U').2]
  exact Zone.nearV s ((H.targeting p he).shrink (q':=t) (by change separation t t+(X.B/2+1) ≤ _; rw [separation_self]; omega))
end Borough
end YM.ConnectedActivityE6
