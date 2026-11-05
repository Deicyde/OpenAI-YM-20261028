import YM.RG08.Canon.Origin
/-! # Extract the balance identity on sectors prior to the limits.
Charge α cost independent of whatever representation filtration approved.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset Next.Free Matrix FreeResolvent Reflect Bloch UVExt.Paths Conductor
open PertExtension.Series.Radial PertExtension.Chart PertExtension.GaussianScore
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f : ℕ→Side} {G : Gauge} {S : ∀ i,StepData (c i) (f i)} {F : ∀ i, Forest (S i).ratio} {p q : Clip} {R T : PathData G} {σ M Λ α σ' M' Λ' A η C : ℝ} {ρ : ∀ i,fieldDir G (c i) 1 → AxisChart G (F i)} {D : ChartRatio G} {Q : Pot G 2} {Y : Air G} {Z : ℕ→Air G} {ν : G.ColorIndex}

lemma income_point (hd:T.Bounds p σ M Λ)(hc:∀ i:ℕ, Tensor.coeff (loopFn T (f:=c i)) 2 0=recital Q (c i)) (hh:Tendsto (fun i=> (c i).val) atTop atTop) (h:Tunable Q)(ht:Glows Q)(u:G.ColorIndex) : probeK u Q=0 := by
  -- Filing carries rays
  obtain ⟨hF,hG⟩:= filing_ready T hd
  let P:= gallery Q; let L:=filing T; let V (i:ℕ) :=loopFn T (f:=c i)
  have he := floors_mark (k:=c) (V:=V) (H:=V) (Q:=L) (δ:=fun _=>0) (by intro i p j k; dsimp; rw [mul_zero,sub_self,norm_zero]) tendsto_const_nhds (Mending.one Q ht) (fun i=>h) hc (fun i j=>(hF i j).1) (fun i=> hG _) hh
  let a:Axis:= 1; let i:Ink G 2:= ![u,u]; let v:= (![coord a,coord a]:Run 2)
  have hu : pressLens P i a a=pressLens L i a a:= funext fun j=> (he i v _).symm
  have hA : AnalyticAt ℝ (pressLens L i a a) 0:= priceL (f:=L) (fun i j=>(hF i j).1) i a a
  have hx : Rays 4 (pressLens L i a a) := by
    intro p; have hb:= (hF i v).2 (roads p)
    unfold pressLens; simp only [map_smul]; exact hb
  unfold probeK alphaPay leapTip; rw [hu]; unfold speedy Tensor.diagonal Tensor.coeff; rw [(rays_jet hA _|>.1 hx) 2 (by decide)]; simp
lemma post_float (P:SummitC S F p q R T ρ D Q Z Y)(hk: T.Bounds q σ M Λ)(hd:∀ m,Chain.Packed ν Q (correct ν Y Q) ∧ Faithful Q Y m)
    (hQ:probeK ν Q=1)(hf: Gets Y)(hp:Tunable Q)(hw: Glows Q)(H:Tendsto (fun i=>(c i).val) atTop atTop) (hS:G.Simple)
    (hM:∀ i,FiniteBound (F i) R T p q α D (ρ i) A η C)(hA:0 ≤ A)(hC:0≤C)(hh:0<η) :
    compass ν Y 1=α ∧ ∀ m:ℕ, Cask q T (c m) Q (correct ν Y Q) := by
  have he:=record_payment P hk hf hp hw H hM hA hC hh
  have hx:Glows (Y 2 2-α • Q):= by rw [sub_eq_add_neg]; exact (hf.2 _ _).2.plus (by simpa only [neg_smul] using hw.scale (-α))
  have hr := income_point hk he H ((hf.2 _ _).1.sub (hp.scale α)) hx ν
  have ha : probeK ν (Y 2 2)=α:= by
    obtain ⟨x,B,hx,hX⟩:= (hf.2 2 2).2; obtain ⟨y,M,hy,hY⟩:=hw
    rw [probe_diff _ hX (hY.scale α) hx hy,probe_scale ν α hY hy,hQ,mul_one] at hr; exact sub_eq_zero.mp hr
  refine ⟨if_neg (by decide)|>.trans ha,fun m=>?_⟩
  have hm:= turns_analytic T.loop hk.width hk.two (m:=c m)
  let V:=correct ν Y Q
  refine ⟨(strain q T hk).analytic.contDiffAt,fun j hj=> ?_, hm.contDiffAt, fun j hj=>?_⟩
  · rw [classic_mend P hk hf hp hw H j hj, sector_adjust _ _ _ hf.1, reviseLead]
  match j with
  | 0=>
    rw [show loopFn T (f:=c m)=turnSeries T.loop from rfl, Tensor.coeff, (rays_jet hm _|>.1 (turns_low T.loop hk.width hk.two (m:=c m))) 0 (by decide), smul_zero, sector, recital_zero]
  | 1=>
    obtain ⟨v,hv,hz⟩:= ((hd (c m)).1.opens (c m)) 1 1
    rw [← hz 1 (by decide),first_nil hS hv, show loopFn T (f:=c m)=turnSeries T.loop from rfl, Tensor.coeff, (rays_jet hm _|>.1 (turns_low T.loop hk.width hk.two (m:=c m))) 1 (by decide),smul_zero]
  | j+2=>
    have h': j=0:=by omega
    rw [h']; rw [show (0+2)=2 from rfl,sector_unique Q _ (e:=2) (by decide) (by decide) (by decide), show correct ν Y Q 2 2 =_ from deuce ν Y Q 0 hQ]; rw [he m]
    unfold sifting duetT; simp [ha]
end YM.RG08.Canon
