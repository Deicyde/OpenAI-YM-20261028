import YM.RG12.Burst.Rich
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy.Charity.RG12
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters Blaze.March
variable (Q : YM.ConnectedActivityE6.Target G P) (L:Side) (μ : ℝ) (hm:0<μ)
    {b : ℝ} (j n i:ℕ)(B s:ℝ→ℝ)(hB:Rate G L 0 B) (hR:Rate G L b s)(hb:0≤b)

lemma degree10 {t:ℝ} (U:ℝ→ℝ) (hU : Rate G L t U) (E:ℝ): Rate G L t (fun x=> degreePrice (radiusB x) (U x) E):=by
   unfold degreePrice Trees.stretch; have he:=Census.width_rate G L 1 0; simp only [one_mul,add_zero] at he; simp_rw [div_eq_mul_inv]
   simpa only [zero_add] using! (((he.mul hU).mul_right _).mul_left _)
include hm hR
lemma root10 : Rate G L (b+Q.rate) (fun x=> s x*(Q.costs L μ 1 x 0).rootHit) ∧ Rate G L (b+Q.rate) (fun x=> s x*(swing Q L μ 1 x 0).rootHit) :=by
   have hp:= Q.rate_root L hm (β:=1) (C:=0)
   exact ⟨hR.mul hp,hR.mul (hp.add (Rate.power.mul_right _))⟩
include hB hb
lemma prize10 : Rate G L (b+Q.rate) (fun x=> Q.goal L x+ value10 Q L μ x (s x) (B x) j n):=by
    obtain ⟨hp,ht⟩:=root10 Q L μ hm s hR
    let e:= fun y:ℝ=> Reserves.extract Q.ε n 0 0*Reserves.treeYield y (1/2) 0
    have he g (hg : Rate G L (b+Q.rate) g) : Rate G L (b+Q.rate) (fun x=> e (g x)):=by unfold e Reserves.treeYield; rw [pow_zero]; simp only [mul_one]; exact (hg.mul_right _).mul_left _
    have hx:Q.rate≤ b+Q.rate:=by linarith
    have hv:= (((hB.mul (he _ hp)).add ((hB.mul (he _ ht)).mul_left 2)).mul_left (2^(j+2):ℝ)); rw [zero_add] at hv; exact (Rate.power.weaken hx).add hv
lemma oil10 (E : ℝ) : Rate G L (b+Q.rate) (fun x=> paint10 Q L μ x (s x) (B x) j n E i):=by
    have he : Rate G L 0 shiftG := (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4
    have hp : Rate G L 0 (fun x=>collars G E x j i):=by simpa only [zero_mul] using! ((he.pow (i*j)).mul_right (Reserves.polyPrice E (i*j)))
    unfold paint10; simpa only [zero_add] using! hp.mul ((prize10 Q L μ hm j n B s hB hR hb).mul_right _)
-- exact desirable stretched unit charge based on \chi^b; any strictly below -Q.rate. Don't claim Lambda cost or use without post-absorption.
def cash10 (Q : ConnectedActivityE6.Target G P)(L:Side)(μ x s B:ℝ)(j n:ℕ)(E:ℝ)(i m:ℕ):ℝ:= (s^m)⁻¹* (Q.goal L x)⁻¹* paint10 Q L μ x s B j n E i
omit hR in
lemma paid10 (m:ℕ)(E : ℝ) : Rate G L (-b*(m:ℝ)+b) (fun x=>cash10 Q L μ x ((betaF G x L)^b) (B x) j n E i m):=by
    let s x:= betaF G x L^b
    have hs:Rate G L b s:=Rate.power
    have hz : Rate G L (-Q.rate) (fun x=>(Q.goal L x)⁻¹):=by apply Rate.congr Rate.power; filter_upwards [Delay.shift_pos G L] with x hx; unfold ConnectedActivityE6.Target.goal; rw [Real.rpow_neg hx.le]
    have hM: Rate G L (-b*(m:ℝ)) (fun x=>(s x^m)⁻¹):=by apply Rate.congr Rate.power; filter_upwards [Delay.shift_pos G L] with x hx; unfold s; rw [← inv_pow,← Real.rpow_neg hx.le,Real.rpow_mul_natCast hx.le (-b) m]
    unfold cash10; convert! ((hM.mul hz).mul (oil10 Q L μ hm j n i B s hB hs hb E)) using 1; ring

omit hB hb in
lemma ready10' (ht:b+Q.rate<0) : ∀ᶠ x:ℝ in atTop, degreePrice (radiusB x) ((s x)*(Q.costs L μ 1 x 0).rootHit) Q.δ ≤ 1/2 ∧ degreePrice (radiusB x) ((s x)*(swing Q L μ 1 x 0).rootHit) Q.δ≤1/2:=by
    obtain ⟨h,h'⟩:=root10 Q L μ hm s hR
    filter_upwards [(degree10 L _ h Q.δ).below ht (1/2) (by norm_num),(degree10 L _ h' Q.δ).below ht (1/2) (by norm_num)] with x hx hX
    exact ⟨(le_abs_self _).trans hx,(le_abs_self _).trans hX⟩
lemma ready10 (ht:b+Q.rate<0) (E:ℝ) : ∀ᶠ x:ℝ in atTop, degreePrice (radiusB x) (Q.goal L x+ value10 Q L μ x (s x) (B x) j n) E ≤1/2:=by
    filter_upwards [(degree10 L _ (prize10 Q L μ hm j n B s hB hR hb) E).below ht (1/2) (by norm_num)] with x hx
    exact (le_abs_self _).trans hx
end YM.PhysicalNext.Repeat.Daisy.Charity.RG12
