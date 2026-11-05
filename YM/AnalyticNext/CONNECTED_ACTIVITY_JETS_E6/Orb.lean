import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.AirG
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Cincture
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Erosion
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Turns

/-!
# V-analytic script local and frame-gauge under shift

No changes Warm. Need χ validation for powers inverse cross ratio.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Vine
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Frond  Scroll Hues LocalRows Rotation
variable {v z r Q s y W : ℝ}
variable {X X' : Coat T F}

section near
variable {a : Site c} {d : ℕ} (p : Room P S T X.x) (H : Zone X X' a d)
include H p
lemma local_strain (i : Mention c f) (h:a=root S i) (he : 12*X.B≤d) (u w : Directions G f)
    (hx : ∀ i,distAt S i a ≤ X.B → X.Hot i →u i=w i) : strain X i.1 i.2 u=strain X' i.1 i.2 w := by
  have hp := H.real p _ _ h he u w hx; unfold Coat.realPath request at hp
  let s:=i.fst; let o:= focus S i.snd
  have hh : AgreeNear id o (X.B/4) (pull s 0 X.V) (pull s 0 X'.V) :=
    Zone.nearV _ (H.pay.shrink (by have hx:100≤X.B:=p.sight.1; change separation a (root S i)+ (X.B/4+1)≤_; rw [h,separation_self]; omega))
  rw [← H.temp, costsX p i.snd hh] at hp
  unfold strain freely; rw [← H.temp, shoreVisa p i.snd hh]
  unfold Coat.R at *; rw [← H.temp] at hp ⊢
  have ht (u v w x s t:G.Color) (h : u-v+w=x-v+s) : u-t+w=x-t+s := by
    calc
      _ = (u-v+w)+(v-t) := by abel
      _ = _ := by rw [h]; abel
  exact ht _ _ _ _ _ _ hp
lemma local_bill (q : Tubular f G) (h:a=along S q) (he : 13*X.B≤d) : leanB X q=leanB X' q := by
  unfold leanB Matrix.mulVec dotProduct; refine sum_congr rfl fun j _=>?_; dsimp only; rw [transpose_apply, transpose_apply]
  by_cases ht: separation a (aim S j) ≤ X.B/4
  · rw [(H.coupling p q h he j).1 ht q]; apply congr_arg
    let Z := H.tune_down (q:=root S j.1) (b:=12*X.B) (by change separation a (aim S j)+_≤_; omega)
    simp only [stand,bar,show X.selected j.1.1 (spot S j.1.2) ↔ _ from Z.shifting j.1.1 (spot S j.1.2) (by rw [addr,← cost_is_here]; rfl) (by omega), local_strain p Z j.1 rfl le_rfl 0 0 (by simp)]
  obtain ⟨hx,hq⟩:= (H.coupling p q h he j).2 ht; rw [hx,hq,zero_mul,zero_mul]
lemma local_voltage (i : Bond f) (h:a=atEdge S i) (he:17*X.B≤d) : voltage X i=voltage X' i := by
  unfold voltage; ext j; change well X (i,j)=well X' (i,j)
  unfold well; simp only [Pi.neg_apply]; apply congr_arg Neg.neg; unfold Matrix.mulVec dotProduct; refine sum_congr rfl fun u _=>?_
  dsimp only; rw [transpose_apply,transpose_apply, ← H.changeL p (i,j) h u (by omega)]; by_cases hg : separation a (along S u) ≤ X.B+2
  · rw [local_bill p (H.tune_down (q:=along S u) (b:=13*X.B) (by have hs:100≤X.B:=p.sight.1; omega)) _ rfl le_rfl]
  rw [h,separation_comm] at hg; rw [kernelA,X.shutter.thin _ u (i,j) (lt_of_not_ge hg),zero_mul,zero_mul]
end near

section
variable (X : Coat T F) (p : P.Funds S T) (h : ShellAccess S G X.x W X.width Q) (z : Site c→G.El)
include p h
lemma reroot (u : Directions G f) (s : Signed) (q : Rod c f) : strain (sluice X z) s q (spinRow S z u)=G.adjoint (z (root S (s,q))) (strain X s q u) := by
  unfold strain; rw [Hues.pockets X h z u]; let U:=gauge z X.V; let Z:Site c→G.El := z ∘ s.act
  obtain ⟨_,_,hp,-⟩:=p.feeds
  change freely T X.x (pull s 0 U) (choice s X.k) q+ orientedRow T X.R s q U _ = _
  rw [show pull s 0 U=_ from X.stillbase (s,q) z,oriented_under T hp,peony _ p, map_add]; rfl
lemma fastens : let Y:= sluice X z; let E:= sheen X z
    leanB Y=E *ᵥ (leanB X) ∧ well Y=E *ᵥ well X ∧ voltage Y = spinRow S z (voltage X) := by
  intro Y E; let a:=sheen X z; let b:=colorwise (z ∘ root S)
  have hx : stand (bar Y 0)= b *ᵥ stand (bar X 0) := by
    rw [shade_act]; funext i
    have hp p' : bar Y 0 p' = G.adjoint (z (root S p')) (bar X 0 p') := by
      unfold bar; by_cases ht' : X.selected (Prod.fst p') (spot S (Prod.snd p'))
      · change (if X.selected _ _ then _ else _)=_
        rw [if_pos ht',if_pos ht',map_smul]
        have he := reroot X p h z 0 p'.1 p'.2
        rw [show spinRow S z (0:Directions G f)=0 from funext fun _=> map_zero _] at he
        exact congr_arg (Coat.scale • ·) he
      change (if X.selected _ _ then _ else _)=_
      rw [if_neg ht',if_neg ht',map_zero]
    exact congr_arg (fun p:G.Color=> p i.2) (hp i.1)
  have hY : Y.form*a=b*X.form := X.contract_step z p
  have hk : leanB Y=E*ᵥ leanB X := by
    unfold leanB; rw [hx,Matrix.mulVec_mulVec,show Y.form.transpose*b=E*X.form.transpose from toss hY (inverse_up _) (inverse_up _), Matrix.mulVec_mulVec]
  have hv : well Y=E *ᵥ well X := by
    unfold well; rw [hk, Matrix.mulVec_neg,Matrix.mulVec_mulVec,show Y.kernelA.transpose*E=E*X.kernelA.transpose from toss (kernelCon X z p) (inverse_up _) (inverse_up _), Matrix.mulVec_mulVec]
  refine ⟨hk,hv,?_⟩
  unfold voltage; rw [hv,shade_act]; rfl
end
end YM.ConnectedActivityE6.Blaze.Vine
