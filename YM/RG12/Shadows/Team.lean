import YM.RG12.Shadows.Money
/-! Retain order per temperature on bona fide projections on Hot platform -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Sanction
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism Brim Lotus Peak
open WardBin.Lies Push.PriceCompiler Foramen Gate Planned.AtomRegular.Foliage
open YM.RG12.Shadows
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{V:Loom G}
open March Daisy Daisy.Charity Greenbelt
structure Crease {E : Type*}[NormedAddCommGroup E][NormedSpace ℝ E](n:ℕ)(w:ℝ)(f:E→ℝ) :Prop where
   head:ContDiffAt ℝ (↑n) f 0
   law:normJ 2 f 0≤w
namespace Crease
variable {n:ℕ}{E:Type} [NormedAddCommGroup E][NormedSpace ℝ E]{w:ℝ}
lemma congr {f g:E→ℝ}(h:Crease n w f)(he:g=ᶠ[𝓝 0] f):Crease n w g:= ⟨h.head.congr_of_eventuallyEq he,by rw [normJ,(he.iteratedFDeriv (𝕜:=ℝ) _).eq_of_nhds]; exact h.law⟩
lemma avg {A:Type}[Fintype A][Nonempty A]{f:A→E→ℝ}(hn:2≤n)(h:∀ i,Crease n w (f i)):Crease n w (fun y=> likely (fun i=>f i y)):=by
  let v:ℝ:= (Fintype.card A:ℝ)⁻¹
  have ha:0<(Fintype.card A:ℝ):=by positivity
  have hx:0<v:= inv_pos.mpr ha
  have he: (fun y=> likely (fun i=>f i y))= v • (∑ i,f i):=by funext x; simp only [likely,Pi.smul_apply,Finset.sum_apply]; rfl
  have hh:ContDiffAt ℝ (↑n) (∑ i,f i) 0:=by simpa only [←Finset.sum_apply,show (fun x:E=>(∑ i,f i) x)=(∑ i,f i) from rfl] using! ContDiffAt.sum (s:=Finset.univ) (f:=f) (fun i _=> (h i).head)
  rw [he]
  refine ⟨hh.const_smul v,?_⟩
  rw [normJ,iteratedFDeriv_const_smul_apply (hh.of_le (Nat.cast_le.mpr hn)),norm_smul,Real.norm_of_nonneg hx.le,iteratedFDeriv_sum_apply (fun i _=> ((h i).head.of_le (Nat.cast_le.mpr hn)))] -- check
  apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) hx.le).trans; apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _=>(h i).law)) hx.le).trans_eq; unfold v; rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ, inv_mul_cancel_left₀ ha.ne']
end Crease
variable {P:Teller G}{c f:Side}{S:StepData c f}{T:Tube G S}
    {B B':BudgetPoint}{Y:Support c}{K:Support f}{w μ x C':ℝ}{R:Rep G f}{p j n m k:ℕ}{L:Side}{Q:ConnectedActivityE6.Target G P}{o:ConnectedActivityE6.Target.Order G w}
variable {d A t C z r η v b Y' q M:ℝ} {C₀:Libretto G n}
variable (H:Cash w x μ L Q o C T R)(U:Leaf R)(i:ℕ)(hx:U.turn=.logKey i)(D:Record)(κ q':Chi)(ε:ℝ)(hN:Captain H p C' d v t A b r M q m Chi.canonical)(hR:Herd H hN.conduit A M m) (L':Config G f→ℝ)(h':R.p.Regular (R.activities.reg i).support L') (hm:U.ingredient= masked R.p.threshold (R.activities.reg i).support L')
    (hp:Plays C₀ D B R.p P T x)(hB:B.B= radiusB x)(hn:B.order≤p)(hk:coverNumber B.B (plate H i).support≤ B.B)
local notation "qL"=> Chi.canonical
local notation "f!"=> Charity.matin U H (Brim.icon H i) (qL)
local notation "g!"=> fun V:Config G c=> Mercury.groves H i D κ q' ε V L'
-- consumer extracted Crease on hymn and occurrence genuine U. From Sanction all required ForE. Uses aggregate signs not run.D.Use direct Crease on trajectories.T. no hB etc except providing arcs.A0.AP.Preserve Scope.
include hx h' hN hR hp
lemma stands (hn': B.order ≤ p)(hg:2≤n) (l : List (Directions G c))(hl:l.length=2)
    (hh:∀ (F:Forest S.ratio)(s:S.Choices), let X:= foyer H i F Chi.canonical (1:Config G c) s; let V := journey 1 l.length l.get ;
       Crease n z (fun x=> U.cinema (vary X (V x)) (Brim.head i) w o.a Q.table Q.halo (podium S G (plate H i).support (radiusB (X.x)))- (mapcase H i F).hymn T (gStep R.beta) q' ε s L' (magic D R.p R.beta κ) 1 (V x))): ‖leftDerivs (f!) l 1-leftDerivs (g!) l 1‖ ≤ z:=by
  let f:= (f!); let g:= (g!)
  let v:= journey 1 l.length l.get
  have hv:Healthy B.threshold (plate H i).support (1:Config G c):= Next.Foundations.one_healthy _ _ B.threshold_pos.le
  have hT: B.order=n:=hp.rehearsed.test
  have hV:Healthy (Pressure.temp x) (plate H i).support (1:Config G c):= hp.rehearsed.temp_eq ▸ hv
  let h (F:Forest S.ratio)(s:S.Choices) := Mercury.hore H i D κ q' ε L' F s
  let Yy (F:Reserve S)(s:S.Choices)(x:Panels l.length):= U.cinema (vary (foyer H i (allot F) (qL) 1 s) (v x)) (Brim.head i) w o.a Q.table Q.halo (podium S G (plate H i).support (radiusB (foyer H i (allot F) (qL) 1 s).x)) - h (allot F) s (v x)
  letI : Nonempty (Forest S.ratio):= Tree.select _ S.patch.odd_side
  have he:Crease n z ((f-g)∘ v):=by
    apply (Crease.avg (f:=fun i x=> likely (fun s=> Yy i s x)) hg (fun F=> Crease.avg hg (h:= fun s=> hh (allot F) s))).congr
    filter_upwards [eventually_all.mpr (fun (s:Reserve S)=> Mercury.embers H U i (qL) (1:Config G c) (allot s) l.get hV hN)] with y hy
    have hb':Brim.icon H i=chip H (Brim.once H i):=rfl -- chip?
    change Charity.matin .. -Mercury.groves ..= _; rw [hb',chip_m]; unfold escort Mercury.groves likely; rw [←mul_sub,←Finset.sum_sub_distrib]; apply congr_arg; apply Finset.sum_congr rfl; intro s hs
    change U.picture (prism T x (qL) o.K (v y) (allot s)) (Brim.head i) w o.a Q.table Q.halo-likely _=likely _; rw [hy]; unfold likely; rw [←mul_sub,←Finset.sum_sub_distrib]; rfl
  have hg' : Push.Local.Chart n f (1:Config G c) := hT ▸ ((Mercury.cornice H U i hx D (qL) hN hp hR hn').smooth 1 hv)
  have hf := (Mercury.masts H i D κ q' ε 1 hp L' h' hv).1
  have h0 : l.length ≤ n:= by omega
  let Ts(e:Config G c→ℝ):=iteratedFDeriv ℝ l.length (e∘v) 0
  have hs(e:Config G c→ℝ)(he: Germ n e 1):leftDerivs e l 1=Ts e cart:=by simpa only [List.ofFn_get] using Germ.ordered l.get (he.prod h0)
  rw [hs f hg',hs g hf]; rw [show Ts f cart - Ts g cart= Ts (f-g) cart from ?_]; swap
  · unfold Ts
    have ht(F:Config G c→ℝ)(hF:Germ n F 1):ContDiffAt ℝ (↑l.length) (F∘v) 0 := by apply WardBin.Lies.Germ.journeys l.get (hF.prod h0) -- find
    change iteratedFDeriv ℝ _ _ 0 _ - iteratedFDeriv ℝ _ _ 0 _ = iteratedFDeriv ℝ l.length ((f∘v)-(g∘v)) 0 _; rw [iteratedFDeriv_sub_apply (ht f hg') (ht g hf), _root_.sub_apply]
  have ht: ‖Ts (f-g)‖ ≤ z:= by
     change normJ _ _ _ ≤ _
     conv_lhs => arg 1; rw [hl]
     exact he.law
  simpa only [Finset.prod_const_one,mul_one] using! ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le ht (show ∀ i:Fin l.length, ‖WardBin.Lies.cart i‖≤ (1:ℝ) from fun i=> (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun j => by simp only [WardBin.Lies.cart,Pi.single_apply]; split <;> norm_num))
end YM.PhysicalNext.Repeat.Sanction
