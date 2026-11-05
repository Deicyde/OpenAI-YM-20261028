import YM.UVExtension.Concert.Vistas

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Concert
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost Wick Wick.Bower MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a : ℝ}
open Animals Reserves Gas Ursell Trees Multiple Letter OmitClusters
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C u D d r q' A v' g w b' Y' n:ℝ} {K l j : ℕ} {χ:Chi} {Q : YM.ConnectedActivityE6.Target G P}
    {o : Target.Order G W} {H : Cash W x μ L Q o a T R} {V : ι→ Juice G f}
open March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt Wick
open AnalyticBridge VerifiedReset Quotes
lemma basisE (Q:YM.ConnectedActivityE6.Target G P) : ∃ m:ℕ,∀ (L:Side),m ≤ L.val →∀ (D:Patch) (χ:Chi) (W μ:ℝ) (o:Target.Order G W), D.Branches P.bind G → 0<W → 0<μ →∀ (N j ℓ :ℕ) (γ e c:ℝ), 0 < c → c < Q.exp→ 0<e→ Q.rate+e<γ → γ<0 → ∃ θ : ℝ → ℝ, Rate G L γ θ ∧ ∀ᶠ x in atTop, ∀ (c' f:Side)(S:StepData c' f), S.patch=D→∀ (T:Tube G S)(R:Rep G f)(A:ℝ)(H: Cash W x μ L Q o A T R), Stamp T→∀ (ι:Type)[Fintype ι] (V:ι→ Juice G f), Fintype.card ι=N→∀ (w:ℝ)(h:Festa Q L H V w (betaF G x L ^ e)) (p:BudgetPoint)(J:(d:Canvas (betaF G x L) w ι)→ Cash W x μ L Q o A T (freshen d R V)), preExponent p≤ c → p.order≤j → p.power ≤ ℓ → p.threshold=temp x→p.B=radiusB x →
    (∀ d,smoothP p (Beam.dashboard H) (Song.sequence H (fleet d J H) χ)) ∧ Nonempty (ticketR (aperture h) p (Beam.dashboard H) (preExponent p) (fun d=> Song.sequence H (fleet d J H) χ) (fun _=> θ x)) := by
  obtain ⟨n,hN⟩:= buyers Q; obtain ⟨m,hm⟩:= entrance P Q; use n+m; intro L hL D χ W μ o hD hW hu N j ℓ γ e c hc hx he h hγ
  obtain ⟨Z,hZ,hq⟩:= March.oar G j; let t x := 2*Pressure.fiery G x L
  have he' : Rate G L (-(1/2)) t:= Rate.flame.mul_left 2
  let v x := ((j:ℝ)+1)*Z*t x
  have hh : Rate G L (-(1/2)) v:= he'.mul_left _
  have hp : ∀ᶠ x : ℝ in atTop, 0<t x := ((Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun x h=> mul_pos (by norm_num) (Work.E09.temp_pos h)
  let b:=(Q.exp-c)/3; have hB:0<b:=by unfold b; linarith
  obtain ⟨θ,hθ,hp'⟩:= hN L (by omega) D χ W μ o hD hW hu v hh (hp.mono (fun x h=>by unfold v; positivity)) N j γ e b hB (by unfold b; linarith) he h hγ
  let s x:=(2:ℝ)^j*θ x; let u x:= |s x|+betaF G x L^γ; let Y x:=guide G b x j ℓ (u x)
  have hb : Rate G L γ u:= ((hθ.mul_left ((2:ℝ)^j)).compare (Eventually.of_forall (fun x=>by simp [s]))).add Rate.power
  have he' : Rate G L 0 shiftG := (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4
  have ht: Rate G L γ Y:=by
    let hv := (((he'.pow (ℓ*j)).mul_right (Reserves.polyPrice b (ℓ*j))).mul_left 2).mul (hb.mul_right (1-1/2)⁻¹); rw [zero_mul,zero_add] at hv; exact hv
  have ht' : Rate G L 0 (fun x=> (Animals.ballCost (radiusB x):ℝ)) := by simpa only [one_mul,add_zero] using! (Census.width_rate G L 1 0)
  have hk: Rate G L γ (fun x=> degreePrice (radiusB x) (u x) b) := by
    have h:= ht'.mul hb; rw [zero_add] at h; simpa only [degreePrice,Trees.stretch,div_eq_mul_inv] using! ((h.mul_right b⁻¹).mul_left 4)
  obtain ⟨A,a,C,d,v',t',r,B,q,k,-,-,hT⟩:= hm L (by omega) D hD j χ W hW μ hu o
  refine ⟨Y,ht,?_⟩
  filter_upwards [hp,hp',hk.below hγ (1/2) (by norm_num),hT,Delay.shift_pos G L] with x hy hp hc hD hYP c' f S hz T R U H hS ι inst V hL w hF p J hU hP hZ' hW hr
  have hf:∀ d,smoothP p (Beam.dashboard H) (Song.sequence H (fleet d J H) χ):= fun i hi=> (Beam.see H hi).symm ▸ (show p.Regular (Song.perf H hi) (Song.sequence H (fleet i J H) χ hi) from (Song.pocketScore p H (fleet i J H) χ (hD _ _ S T hz hS _ U (J i)).some hW hP ℓ hZ' hi).1)
  refine ⟨hf,?_⟩
  obtain ⟨A,b',B,C,r,d,n,k,U,Z',c,l,hx,Y'',hY⟩:= hp
  have hm : temp x ≤ t x:= by have he:= H.laws.data.room.temperatures; rw [H.laws.data.funds.length_eq] at he; exact he
  have he : Sailor G p.threshold (Z*t x) j:= ⟨fun c A hA=> hq c _ hy.le A (hA.trans (hW.trans_le hm))⟩
  let H':= hY c' f S T _ R H hS hz.symm ι hL V w hF
  refine visaE (N:=hz.symm ▸ Y'') hS hF H' J hW hr hP he (mul_nonneg hZ.le hy.le) (by unfold v; nlinarith [mul_nonneg hZ.le hy.le]) hB (by unfold u; positivity) (by unfold b at *; linarith only [hU]) ?_ ((le_abs_self _).trans hc) ℓ hZ' hf
  rw [← hx]; exact (le_abs_self (s x)).trans (le_add_of_nonneg_right (Real.rpow_nonneg hYP.le _))
end YM.UVExtension.Concert
