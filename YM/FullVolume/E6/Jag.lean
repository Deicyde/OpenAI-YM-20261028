import YM.FullVolume.E6.Fires
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open FullVolume.Neptune Flux Shield Eider Packets Polar
open Poll
lemma watt {ι:Type}[Fintype ι](u: Body ι)(i): |u i|≤‖u‖:=by rw [← EuclideanSpace.basisFun_inner]; exact (abs_real_inner_le_norm ..).trans_eq (by rw [OrthonormalBasis.norm_eq_one,one_mul])
lemma facetsP (I:Finset (Bond f)):∃ C:ℝ,0≤C∧ ∀ z:Air f G,1 ≤ facescale I z ∧ facescale I z ≤ C*(1+‖z‖):=by
    let P:=lensS I G; let v:ℝ:= P.card; refine ⟨(1+(I.card:ℝ)+v),by unfold v; positivity,fun z=>⟨(expenses I z).1,?_⟩⟩; have h:=Finset.sum_le_sum (s:=P) (f:=fun j=> |z j|) fun i _=>watt z i; rw [sum_const,nsmul_eq_mul] at h
    unfold facescale; unfold v P at *; nlinarith [Nat.cast_nonneg (α:=ℝ) I.card,norm_nonneg z]
variable {M:Bank}(I:Depot Q o x μ L C₀ K) {χ: Chi} [CompleteSpace E]
set_option quotPrecheck false
include I
variable (X:∀ n,Coat (K n).tubes F)(hx:∀ n,(X n).x=x)(hK:∀ n,(X n).width=o.K)(hm:∀ n,(X n).manifest)
include hx hK hm
local notation "H'"=> fun n y=> (X n).wrapY y
local notation "b"=> fun n=> (K n).beta
lemma ladders (n): Allow (X n|>.relating) (along (G:=G) S) (tubularPrice G L) (retain o.eta o.gap o.ample) (o.ample⁻¹/2) (1+payE o.eta o.gap o.ample (tubularPrice G L)):= Rotator.suspected (X n) ((I n).laws.data.localP F (X n) (hx n) (hK n) (hm n)).sails
private lemma tipN : ∃ C:ℝ, 0≤ C ∧ ∀ n y, ‖tip (H' n y)‖≤ C :=by
    let C:= o.cap*Pressure.fiery G x S.patch.L; let D:= Fintype.card (Tubular f G)*(C^2); have hh : 0 ≤ D := by unfold D; positivity
    refine ⟨Real.sqrt D, Real.sqrt_nonneg _,fun n y=>?_⟩
    let U:= H' n y; let t:=tip U; have hv i: ‖voltage U i‖≤ C:=by
          have hj:= (I n).laws.data; have hU:= (hj.safety).2.2.2 F U (hx _) (hK _) (hm _); rw [← agrees_all U (show Room P S (K n).tubes _ from (hx n).symm ▸ hj.room) (hm n)]; unfold C; rw [← hx n]; exact hU.1 _
    apply le_of_sq_le_sq _ (Real.sqrt_nonneg _); rw [Real.sq_sqrt hh,EuclideanSpace.real_norm_sq_eq]
    refine (sum_le_sum (g:=fun _=>C^2) (fun i _=>?_)).trans_eq ?_; swap; · simp only [sum_const,nsmul_eq_mul,card_univ]; rfl
    change t i^2≤ _; rw [← sq_abs]; apply pow_le_pow_left₀ (abs_nonneg _); exact (watt (voltage U i.1) _).trans (hv i.1)
omit I hx hK hm in
private lemma caged (B u v τ:ℝ)(hB:0≤B)(hu:0<u)(ht:0<τ) (w t :Air f G) (r:ℝ)(he:‖t‖≤B)(h:u≤r) (hv:r≤v) :
     let z:= r • (w-t); 1+‖z‖ ≤ (1+v+v*B)*(1+‖w‖) ∧ Real.exp (-τ*‖z‖^2) ≤ Real.exp (τ*u^2*B^2)*Real.exp (-(τ*u^2/2)*‖w‖^2):=by
    intro z; have hh:0<r:=hu.trans_le h; have hf:0<v:=hh.trans_le hv; rw [show z=r • (w-t) from rfl,norm_smul,Real.norm_of_nonneg hh.le]
    constructor
    · have hp := mul_le_mul hv ((norm_sub_le w t).trans (add_le_add_right he _)) (norm_nonneg _) hf.le; nlinarith only [hp,hf,hB,norm_nonneg w,show 0≤v*B*‖w‖ by positivity]
    rw [←Real.exp_add]; apply Real.exp_monotone
    have he': ‖w‖ ≤ ‖w-t‖+B:= by nth_rw 1 [show w=w-t+t from (sub_add_cancel ..).symm]; exact (norm_add_le ..).trans (add_le_add_right he _)
    have hx:‖w‖^2 ≤ 2*‖w-t‖^2+2*B^2:= by nlinarith [norm_nonneg w, norm_nonneg (w-t), sq_nonneg (‖w-t‖-B)]
    have hs:(u*‖w-t‖)^2 ≤ (r*‖w-t‖)^2:= by gcongr
    nlinarith only [hs,hx,ht,hu, mul_le_mul_of_nonneg_left hx (show 0≤τ*u^2 by positivity), mul_le_mul_of_nonneg_left hs ht.le]
-- brush.toolbox
lemma impartial (J:Finset (Bond f))(k:ℕ) :∃ D:Air f G →ℝ, (∀ w,0≤D w) ∧ Integrable D volume ∧ ∀ n y (w:Air f G), let U:=H' n y; let z:=kickback U (K n).beta w
           0≤ cups U (K n).beta w ∧ cups U (K n).beta w*facescale J z^k ≤ D w:=by
    let r(n:ℕ):=(gStep (K n).beta)⁻¹; let f₀:=betaF G x S.patch.L; let u:=Real.sqrt (f₀/2); let v:= Real.sqrt (2*f₀)
    have hS:1<f₀:=(I 0).laws.intake.height; have hu:0<u:=Real.sqrt_pos.mpr (by linarith); have hv:0<v:=Real.sqrt_pos.mpr (by linarith)
    have hh (n:ℕ):u≤r n∧r n≤v:=by simp only [r,gStep,inv_inv]; exact ⟨Real.sqrt_le_sqrt (I n).laws.intake.window.1,Real.sqrt_le_sqrt (I n).laws.intake.window.2⟩
    obtain ⟨τ,C,ht,hC,hA⟩:= oasis (ladders I X hx hK hm); obtain ⟨B,hB,hV⟩:=tipN I X hx hK hm; obtain ⟨K₀,h₀,hZ⟩:= facetsP (G:=G) J
    let R:=Module.finrank ℝ (Air f G); let b':= C*Real.exp (τ*u^2*B^2); let F':=K₀*(1+v+v*B); let D(w:Air f G):= (v^R*b'* F'^k)*(Real.exp (-(τ*u^2/2)*‖w‖^2)*(1+‖w‖)^k)
    have hi : 0≤F' := by unfold F'; positivity
    refine ⟨D,fun w=>by unfold D b'; positivity, (crystal (show 0<τ*u^2/2 by positivity) k).const_mul _,?_⟩; intro n y w U z
    have hr : 0< r n:= hu.trans_le (hh n).1
    have hf: 0 ≤ cups U (K n).beta w:= mul_nonneg (pow_nonneg hr.le _) (fullFuel ..).le
    obtain ⟨hq,he⟩:= caged B u v τ hB hu ht w _ _ (hV n y) (hh n).1 (hh n).2
    rw [← show z=r n • _ from kickback_eq U (K n).beta w] at hq he
    let g:=Real.exp (-(τ*u^2/2)*‖w‖^2)
    have h': cups U (K n).beta w≤ v^R*(b'*g):= mul_le_mul (pow_le_pow_left₀ hr.le (hh n).2 R) ((hA n z).trans ((mul_le_mul_of_nonneg_left he hC.le).trans_eq (mul_assoc ..).symm)) (fullFuel ..).le (pow_nonneg hv.le R)
    have hz: facescale J z^k ≤ (F'*(1+‖w‖))^k:= pow_le_pow_left₀ (zero_le_one.trans (hZ z).1) ((hZ z).2.trans ((mul_le_mul_of_nonneg_left hq h₀).trans_eq (mul_assoc ..).symm)) _
    exact ⟨hf,(mul_le_mul h' hz (pow_nonneg (zero_le_one.trans (hZ z).1) _) (le_trans hf h')).trans_eq (by unfold D g; rw [mul_pow]; ring)⟩
end YM.ConnectedActivityE6.Lim
