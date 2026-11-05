import YM.RG08.Canon.Window
import YM.RG08.Action.Gallant
/-! # Period-to-cover passage. Keep both metrics on relative mesh.
Canon fields may carry strictly larger held moment witnesses. No annulus assumption.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset Next.Free Matrix FreeResolvent Reflect Bloch UVExt.Paths Conductor
open PertExtension.Series.Radial PertExtension.Chart PertExtension.GaussianScore
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f : ℕ→Side} {G : Gauge} {S : ∀ i,StepData (c i) (f i)} {F : ∀ i, Forest (S i).ratio} {p q : Clip} {R T : PathData G} {σ M Λ α σ' M' Λ' A η C : ℝ} {ρ : ∀ i,fieldDir G (c i) 1→ AxisChart G (F i)} {D : ChartRatio G} {Q : Pot G 2} {Y : Air G} {Z : ℕ→Air G} {ν : G.ColorIndex}

structure SummitC (S : ∀ i,StepData (c i) (f i))(F : ∀ i,Forest (S i).ratio) (p q : Clip)(R T:PathData G) (ρ : ∀ i,fieldDir G (c i) 1 → AxisChart G (F i))
    (D:ChartRatio G)(Q:Pot G 2)(Z:ℕ→Air G)(Y:Air G):Prop where
    headers (i:ℕ) : ShellC (F i) p R (ρ i) D Q (Z i)
    classic (i:ℕ) : ClassicalMatch (F i) p q R T (ρ i)
    mend a r : Mending (fun i=> Z i a r) (Y a r)
    tunes i e j : Tunable (Z i e j)

lemma field_mend (R:SummitC S F p q R T ρ D Q Z Y)(a r:ℕ)(h : Glows Q): Mending (fun i=>sector Q (Z i) a r) (sector Q Y a r) := by
  unfold sector; split; exact Mending.one _ Glows.zero; exact R.mend ..
  next n=> split; next H=> rw [show n=0 by omega]; simpa only [prolong_self] using (Mending.one Q h)
           exact R.mend ..

lemma classic_mend (P:SummitC S F p q R T ρ D Q Z Y)(hk: T.Bounds q σ M Λ)(hf: Gets Y)(hp:Tunable Q)(hw: Glows Q)(H:Tendsto (fun i=>(c i).val) atTop atTop)
      (r) (hr:r≤4)(x:ℕ) : Tensor.coeff (classicFn q T (f:=c x)) r 0= recital (sector Q Y 0 r) (c x) := by
  cases r with
  | zero=> rw [antique (P.headers x) (P.classic x) 0 hr,sector,sector]
  | succ n=>
    obtain ⟨X,w,C,hX,hL⟩:=cart_map n hk
    let V:=fun i : ℕ=> classicFn q T (f:=c i)
    let E t:=sector Q (Z t) 0 (n+1)
    apply floors_equal (Q:=X) ?_ (Tune_sector Y Q (fun e j=> (hf.2 e j).1) hp _ _) (hL (c x))
    have he i := antique (P.headers i) (P.classic i) (n+1) hr
    exact floors_mark (k:=c) (V:=V) (H:=V) (U:=E) (δ:=fun _=>0) (fun i p j k=> by dsimp; rw [mul_zero,sub_self,norm_zero]) tendsto_const_nhds (field_mend P 0 _ hw) (fun i=> Tune_sector _ _ (P.tunes i) hp _ _) he hX (fun i=> hL (c i)) H
-- Thus exact relative subtraction and field-independent reset. tip extraction from Filing.
lemma record_payment (P:SummitC S F p q R T ρ D Q Z Y) (hk: T.Bounds q σ M Λ)(hf: Gets Y)(hp:Tunable Q)(hw: Glows Q)(H:Tendsto (fun i=>(c i).val) atTop atTop)
    (hM:∀ i,FiniteBound (F i) R T p q α D (ρ i) A η C)(hA:0 ≤ A)(hC:0≤C)(hh:0<η) :
     ∀ i : ℕ, Tensor.coeff (loopFn T (f:=c i)) 2 0=recital (Y 2 2-α • Q) (c i) := by
  let t (i:ℕ): (S i).Choices:= Classical.arbitrary _
  let U:= sector Q Y 1 2
  let V m:=draft α T q ∘ arm G m 1
  obtain ⟨P',w,B,hP',hB⟩:=cart_base 1 hk
  let X:= (α:ℂ) • P'+filing T; let d:= min w σ
  obtain ⟨hZ,hT⟩:=filing_ready (R:=T) hk
  have hd (m): V m = α • inputSeries q T +turnSeries T.loop := by
    funext i; rfl
  have hx m : Recorded X (V m) 0:= by
    rw [hd]; let Z:= inputSeries q T (m:=m); have hh := (stain_knit T q hk (m:=m)).analytic
    exact ((hB m).weigh α hh).both ((analyticAt_const (v:=α)).mul hh) (turns_analytic T.loop hk.width hk.two (m:=m)) (hT m)
  set n:= Λ*(reflectBill 1 σ*inheritRate σ)
  have hK a b : Firm d (‖(α:ℂ)‖*B+n) (X a b) := by
    have he := (hZ a b).1.mono (lt_min (hP' a b).width_pos hk.width) (min_le_right w σ) (le_refl _)
    have hh: Firm d B (P' a b):=(hP' a b).mono (lt_min (hP' a b).width_pos hk.width) (min_le_left ..) le_rfl
    exact Firm.add (f:=(α:ℂ) • P' a b) ((Firm.const hh.width_pos (α:ℂ)).mul hh) he
  let δ i:=4*A*C*Real.exp (-η*(c i).val)
  have hδ:Tendsto δ atTop (𝓝 0):= by
    have hv : Tendsto (fun i=> ((c i).val:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp H
    simpa only [δ,mul_zero] using! ((Real.tendsto_exp_atBot.comp (hv.const_mul_atTop_of_neg (show -η < 0 by linarith))).const_mul (4*A*C))
  let Z' i:= aureole R (F i) (t i) p (ρ i) D
  have hu := floors_mark (k:=c) (δ:=δ) (V:=Z') (H:=fun i=> V (c i)) (fun i=> cents_tax (t i) (hM i) hA hC) hδ (field_mend P 1 2 hw) (fun i=> Tune_sector _ _ (P.tunes i) hp _ _) (fun i=> (P.headers i).rope 2 le_rfl (t i)) hK (fun i=> hx (c i)) H
  intro i; let T':=c i
  have hb := (lead_true hk 2 le_rfl T').symm.trans (classic_mend P hk hf hp hw H 2 (by decide) i); rw [sector_t] at hb
  have hd' := floors_equal hu (Tune_sector _ _ (fun i j=> (hf.2 i j).1) hp _ _) (hx T')
  rw [sector_unique Q Y (e:=2) (by decide) (by decide) (by decide),hd] at hd'; let Ξ:= inputSeries q T (m:=T')
  have hY := (stain_knit T q hk (m:=T')).analytic; have hJ:=turns_analytic T.loop hk.width hk.two (m:=T')
  have hv : Tensor.coeff (V T') 2 0= α • (Tensor.coeff Ξ 2 0)+Tensor.coeff (turnSeries T.loop (m:=T')) 2 0 := by
    rw [hd]; unfold Tensor.coeff; rw [iteratedFDeriv_add_apply (show ContDiffAt ℝ (↑(2:ℕ):WithTop ℕ∞) (α • Ξ) 0 from (contDiffAt_const.mul hY.contDiffAt)) hJ.contDiffAt,
      iteratedFDeriv_const_smul_apply hY.contDiffAt, smul_add,smul_comm]
  rw [hd] at hv; change Tensor.coeff (turnSeries T.loop (m:=T')) 2 0= recital (Y 2 2-α • Q) T'
  rw [recital_sub (hf.2 _ _).1.1 (show Summable _ from (hp.scale α).1),recital_scale α hp.1,← hb, ← hd',hv]
  simp only [Ξ,add_sub_cancel_left]
end YM.RG08.Canon
