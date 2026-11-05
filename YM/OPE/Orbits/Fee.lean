import YM.OPE.Orbits.Receipts

/-! Rate paid by the new readers for inserting the old truncation through
H as an auxiliary physical match. Reader horizon and H needn't coincide. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Orbits
open Function Set Filter MeasureTheory Extraction Table
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
attribute [local instance] measO borelO hμ

variable {G:Gauge} {C:Family G}{S:Table C.book}{F:Order}
    (U:Spec.Final C F S) (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (h:Services C F S) {I L:Type} [Fintype I]{A:L→ℝ}{φ:Filter L}(hA:Tendsto A φ atTop) [φ.NeBot]
    {d:I→ℕ}{a b c:ℝ} {x:L→ I→ E4}{o:L→E4} {v:Labels S d} (hx:enveloped φ A a x o)(hk:Kept φ A a x)(ha:0<a)
local notation "Q" => U.sector.derivatives
local notation "P" => R.port
local notation "X" => U.sector.turns
local notation "ρ" => U.room.kernel.spin

private lemma cell_margin (z:E4)(m:ℕ):orbitMargin P m (sole z) z :=by
    convert (translateMargin m (sole 0) 0 z).mpr (centerMargin P m)
    · exact (zero_add z).symm
    exact (zero_add ..).symm

private lemma int_live {q:I→E4}{z:E4}{n:ℕ} (w:Labels S d)(hx:orbitMargin P n q z):Integrable (fun k=>spinning P X n q z k w) haar:=by
    let f i:=bears X P i n q z w; refine Integrable.congr (f:=fun j=>∑ i∈bands Q n,f i j) ?_ (Eventually.of_forall (fun i=> (scatter P R.continuum n q z w i).symm)); exact integrable_finsetSum (bands Q n) (μ:=haar) (f:=f) fun i hi=>integrable_bears P R.law R.continuum n q z i w (hx i hi)
include hA hx hk ha
set_option maxHeartbeats 600000 in
lemma bridge_abstract {m n:ℕ}{z:L→S.Field m} (h:∀ k:L→Ortho, RateLE φ A (fun s=>spinning P X n (x s) (o s) (k s) v - spinning P X n (sole (o s)) (o s) (k s) (sole (z s) : Labels S (fun _:Unit=>m))) b) :
    RateLE φ A (fun s=>averageV P X n (x s) (o s) v-averageV P X n (sole (o s)) (o s) (sole (z s) : Labels S (fun _:Unit=>m))) b:=by
    refine (price_integral (fun (i:L) (k:Ortho)=>spinning P X n (x i) (o i) k v - spinning P X n (sole (o i)) (o i) k (d:=fun _:Unit=>m) (sole (z i))) (μ:=haar) h).congr ?_; filter_upwards [margins U R hA hx hk ha n] with i hi; change (∫ k,_ ∂haar) = _; rw [averageV,averageV,if_pos hi,if_pos (cell_margin U R _ _),← integral_sub (int_live U R v hi) (int_live U R (d:=fun _:Unit=>m) (sole (z i)) (cell_margin U R _ _))]

variable (H:ℕ) -- replace
variable (n:ℕ)
local notation "Z" => fun i:L=>shadowOld R.port H (x i) (o i) v
include h
lemma bridge_averaged : RateLE φ A (fun i=> checkReal P R.law R.continuum n (x i) (o i) v - checkReal P R.law R.continuum n (sole (o i)) (o i) (sole (Z i) : Labels S (fun _:Unit=>H))) ((weight d-H-1)*a):=by
    have hp:= bridge_abstract (z:=Z) U R hA hx hk ha (fit_old U R h hA v hx hk ha H n)
    have ht:= bridge_abstract U R hA hx hk ha (fit_tint U R h hA v hx hk ha H n)
    let V i:= checkReal P R.law R.continuum n (x i) (o i) v - checkReal P R.law R.continuum n (sole (o i)) (o i) (sole (Z i) : Labels S (fun _:Unit=>H))
    have hsum:= hp.add (pay_fixed hA (conjugateR ρ n) ht) hA; have hf:= (RateLE.const (2⁻¹:ℝ) hA).smul hsum
    refine (hf.mono (a:=0+((weight d-H-1)*a)) (by rw [zero_add])).congr ?_
    refine Eventually.of_forall fun i:L=>?_ ; dsimp only; rw [checkValue,checkValue,map_sub, (show bar ρ (d:=fun _:Unit=>H) (sole (Z i))= sole (S.conj U.room.kernel.spin H (Z i)) from rfl)]; change (2⁻¹:ℝ) • _ = _; rw [← smul_sub]; apply congr_arg; abel
lemma fresh_bridge: RateLE φ A (fun i=> R.fresh n (x i) (o i) v - R.cutTest n H (Z i)) ((weight d-H-1)*a):=by
    have hv:=bridge_averaged (v:=v) U R h hA hx hk ha H n; apply (pay_fixed hA ((R.knife n).restrictScalars ℝ) hv).congr; filter_upwards with i
    let g:Labels S (fun _:Unit=>H):=sole (Z i); let c:=o i
    have hh: checkReal P R.law R.continuum n (sole c) c g = checkReal P R.law R.continuum n (sole 0) 0 g:=by
        apply Eq.trans ?_ (checkReal_transfer n R.law R.continuum _ _ _ c); rw [zero_add,(show (fun i:Unit=>sole (0:E4) i+c)=sole c from funext (fun _=>zero_add _))]
    simp only [map_sub]; change _ - R.knife n (checkReal P R.law R.continuum n (sole c) c g) = _; rw [hh]; rfl
end YM.OPE.Orbits
