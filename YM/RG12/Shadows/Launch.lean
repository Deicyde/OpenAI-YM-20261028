import YM.RG12.Shadows.Tupper
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
namespace Bazaar
variable {S:Shows V}(H:Bazaar V S)(T': Anthem V.n) -- edit
local notation "B!" i:max=> S i
local notation "q₀"=> V.patch.L
local notation "T0"=>H.winter
include H T'
lemma leases (κ:Chi):∃ (d e:ℝ)(t:ℝ)(r N W C:ℕ→ℝ), Canary G d e ∧Charges T0 0 N∧ Charges T0 0 C∧(∀ i:ℕ,0 ≤ C i)∧
    (∀ i, C i≥ |altitude T' (N i) (W i) (r i)|) ∧ ∀ᶠ i:ℕ in atTop, (B! i).Quay T' d (r i) (N i) (W i) t κ := by
   obtain ⟨d,e,hE⟩:= Eider.weave G
   obtain ⟨M,X,J,v,l,t,hM,h₀,hX,hJ,hv,ht,hl⟩:= spicules G V.P (q₀) V.patch V.align V.n V.p V.Lib V.D V.depth V.W V.o V.chi
   let K x:=Coat.burst G (q₀) x; let U x:= K x*(5*V.o.a*fiery G x (q₀)+ |V.o.cap| *fiery G x (q₀))
   have hU:Rate G (q₀) 0 U:=by simpa only [add_neg_cancel] using! ((burst_rate G (q₀)).mul (((Rate.flame).mul_left _).add ((Rate.flame).mul_left _)))
   obtain ⟨N,D,Q,hN,hD,hQ,hS⟩:= sweaters G V.P (q₀) V.n T' V.D V.chi κ V.W V.o d e hE hM hX hJ hv ht hU
   let C x:= |altitude T' (N x) (Q x) (D x)|
   have he := b_power V.n T' hN hQ
   have hg := projectionX V.n T' hN hQ (hD.weaken (by norm_num:-(1/2:ℝ)≤0))
   have hB: Rate G (q₀) 0 C:=by
      have hp: Rate G (q₀) 0 (fun x=> Prism.incomeB T' (N x) (Q x)):= (Brim.bell hQ he).mul_right _
      have ha: Rate G (q₀) 0 (fun x=> incomeD T' (N x) (Q x) (D x)):= by unfold incomeD tensor0; exact (Brim.bell hQ ((Brim.bell he (hg.mul_left _)).mul_right _)).mul_right _
      exact absolut (((Brim.bell hp (hQ.mul_left T'.expE)).add (Brim.bell (ha.add hp) hQ)).mul_right _)
   have hd : 0 < d:=hE.warm
   have hk : Rate G (q₀) (-(1/2)+0) (fun x=> 8*V.o.a *fiery G x (q₀)) := by rw [add_zero]; exact Rate.flame.mul_left _
   have hR:= (absolut hJ).mul (Blaze.inverse_mist G (q₀))
   refine ⟨d,e,t,fun i=>D (S i|>.x),fun i=>N (S i|>.x),fun i=>Q (S i|>.x),fun i=>C (S i|>.x),hE,by apply H.froth; rw [zero_div,neg_zero]; exact hN,by apply H.froth; rw [zero_div,neg_zero]; exact hB,fun _=>abs_nonneg _,fun _=>le_refl _,?_⟩
   filter_upwards [H.sums.eventually hl,H.sums.eventually hS,H.sums.eventually (Brim.snip G (q₀) V.P V.D hD),H.sums.eventually (hk.below (by norm_num) _ (half_pos hd)),H.sums.eventually (hR.below (by norm_num) (1/2) (by norm_num))] with i hM hL hT hK hR
   let B:=S i; let x:=B.x; change B.Quay T' d (D x) (N x) (Q x) t κ
   have hx:Rotator V.P (q₀) V.o.eta V.o.gap V.o.ample V.o.indexPay B.X:= by rw [←B.well]; exact B.living.sails
   have hY : coverNumber (radiusB B.x) B.Y ≤ radiusB B.x:= B.hc ▸ B.hx
   have he:=hM B.c B.f B.S B.T B.well B.rise B.H.laws.data.access B.F B.X rfl B.chi B.width B.legal hx B.B B.A.p B.hp B.ho B.I B.Y _ B.a B.q B.b B.u B.hu B.hc B.hx B.curtains B.lynx 2 B.U V.depth B.rail (by rw [← B.well]; exact B.toll)
   have hv:8*V.o.a*B.X.t≤d/2:=by rw [B.tempo]; exact (le_abs_self _).trans hK
   apply B.fuelCast hE (l:=|J x|) (M:=M x) (T':=|l x|) (v:=|v x|) (W:=|X x|) -- l? Tentacle offset=|J x| armies.out =l
   refine ⟨he,?_,hv,?_,?_⟩
   · intro z hz
     have hU : ‖z‖ ≤ U x:= by convert! hz using 1; unfold U K Barque.tongs; rw [B.well,B.tempo]
     have hf:= hL B.c B.f B.S B.T B.F B.X rfl B.rise B.chi hv B.chip B.A B.H.laws.intake B.I B.Y B.a B.q B.b B.u B.hu hY _ _ B.U he z hU
     rw [B.center,←B.well] at hf; exact hf
   · rw [B.tempo]; let F:= fiery G x (q₀); have hf:0<F:= by unfold F x; rw [← B.tempo]; exact B.living.sails.room.fiery
     change |J x| ≤ F/2
     apply le_of_mul_le_mul_right _ (inv_pos.mpr hf); rw [div_mul_eq_mul_div, mul_inv_cancel₀ hf.ne']; exact (le_abs_self _).trans hR
   let hs:=hT _ _ B.S B.T B.A (congr_arg (fun p:Patch=>p.L) B.well) B.H.laws.intake
   unfold Barque.swell; rw [B.well]; exact ⟨hs.1,hs.2.1⟩
omit T' in
lemma banks0: Charges T0 0 (fun i=>(S i).tongs)∧∀ p:ℝ,Charges T0 p (fun i=>Real.exp (-(S i).swell)):=by
   unfold Barque.tongs Barque.swell; simp_rw [Barque.well,Barque.tempo]
   let K x:=Coat.burst G (q₀) x; have hp:Rate G (q₀) 0 (fun x=> K x*(5*V.o.a*fiery G x (q₀)+ |V.o.cap| *fiery G x (q₀))) :=by simpa only [add_neg_cancel] using! ((burst_rate G (q₀)).mul (((Rate.flame).mul_left _).add ((Rate.flame).mul_left _)))
   exact ⟨H.froth _ (by rw [zero_div,neg_zero]; exact hp), fun _=> H.froth _ (waft G (q₀) V.D _)⟩
end Bazaar
end YM.PhysicalNext.Repeat.Sanction
