import YM.FullVolume.E6.Oars
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
open Flux Shield Eider
/-- fixed physical variable `w : Air` including unused colors, inside each Y bill. Transform β separately for each *real integral.* -/
def kickback {T:Tube G S}(X:Coat T F)(β:ℝ)(w:Air f G): Air f G:= WithLp.toLp 2 (stand ((gStep β)⁻¹ • (X.atmos w - voltage X)))
lemma kickback_home {T:Tube G S}(X:Coat T F){β:ℝ}(he:0<β)(w:Air f G) : worldZ X β (kickback X β w)= X.atmos w:=by
    have h:0<gStep β:= inv_pos.mpr (Real.sqrt_pos.mpr he)
    unfold worldZ; change voltage X+gStep β • ((gStep β)⁻¹ • (X.atmos w-voltage X))=_; rw [smul_inv_smul₀ h.ne']; abel
-- density lens Frill with actual Allow. Branch.Carriers at base.^
lemma lensP {ι:Type}[Fintype ι][DecidableEq ι]{M M':ℕ→ E→ Matrix ι ι ℝ}{u w:ℕ→ E→ Poll.Body ι} [φ.NeBot]{i:ι→Site c}{t:ℕ}{η r C:ℝ}(hv:∀ᶠ n in φ,Allow (M n p) i t η r C)(h:Buds φ j p M M')(he:Frill φ j p u w): Frill φ j p (fun n y=> lens₀ (M n y) (u n y)) (fun n y=> lens₀ (M' n y) (w n y))∧∀ l,Tendsto (fun n=> lens₀ (M n p) (u n p)) φ (𝓝 l)→0<l:=by
    let f(Y:Matrix ι ι ℝ)(x:Poll.Body ι):= -Real.log Y.det/2-dotProduct x.ofLp (Y⁻¹ *ᵥ WithLp.ofLp x)/2
    let g(n:ℕ)(y:E):=f (M n y) (u n y); let k(n:ℕ)(y:E):= f (M' n y) (w n y)
    have hG: Frill φ j p g k := (((h.renting hv).neg).via (Q:=fun v:ℝ=> v/2) (contDiff_id.div_const _)).sub ((Frill.buds Finset.univ fun i _=> (pointed he i).times (mvec (h.restoreP hv) (F:=fun n y=>WithLp.ofLp (u n y)) (Gf:=fun n y=>WithLp.ofLp (w n y)) (fun k=>pointed he k) i)).via (contDiff_id.div_const 2))
    refine ⟨(Frill.still _).times (hG.via Real.contDiff_exp),fun l hl=>?_⟩
    obtain ⟨g,hg,-⟩:=hG.crest
    rw [tendsto_nhds_unique hl (show Tendsto _ _ (𝓝 ( ((Real.sqrt (2*Real.pi))^Fintype.card ι)⁻¹ * Real.exp g)) from (tendsto_const_nhds.mul (Real.continuous_exp.continuousAt.tendsto.comp hg)))]; positivity
variable [FiniteDimensional ℝ E] {q d:ℝ}
namespace Draft
variable (H₀:∀ n,Cash W x μ L Q o C₀ (K n).tubes (K n).kin)(T:∀ n,Cash W x μ L Q o C₀ (H n).tubes (H n).kin)(hQ: ∀ n,Promo Q o j x v ℓ a Z.χ (K n).tubes)
   (hz:Z.Paid Q o x) (h:Finish J K H)(he:∀ᶠ i in (J:Filter ℕ), Mode (U i) p j v)(ht:∀ᶠ i in (J: Filter ℕ), Z.Viable (U i p))(hA:Eider.Canary G d q)
set_option quotPrecheck false
local notation "D" => fun n y=> (Z.paints (K n) (U n y))
local notation "D'" => fun n y=> (Z.paints (H n) (U n y))
-- Primal moves. only χ.steer overhead. common w.
include he hA
lemma skipper (i:Bond f): Frill J j p (fun n y=> G.mat (action (D n p) (U n y) i)) (fun n y=> G.mat (action (D' n p) (U n y) i)):= Strand.glowing (Strand.banners J (fun n=> replica S.ratio (U n p) i)) ((scaleG he).books S i|>.inverse)
lemma skipJ (w:Air f G) (i:Bond f): Frill J j p (fun n y=> steerJ (D n p) d ((D n p).atmos w) (U n y) i) (fun n y=>steerJ (D' n p) d ((D' n p).atmos w) (U n y) i):=by
    let L: G.Color :=(D 0 p).atmos w i
    refine (skipper (K:=K) (H:=H) (Z:=Z) he hA i).fares (Q:=fun X:G.Mat=> palm G Z.χ d X L) fun g hg=> ?_
    have ht := hA.side; obtain rfl : g=1:= tendsto_nhds_unique hg (by simp [Silica.action,paints] <;> exact tendsto_const_nhds) -- simp paints
    exact (Eider.lift hA Z.χ _ L (j:=j) (by simp [ht.le])).comp 1 (f:=fun x=> (x,L)) (contDiffAt_id.prodMk contDiffAt_const)
lemma skipperY (w:Air f G): Frill J j p (fun n y=> steer (D n p) d ((D n p).atmos w) (U n y)) (fun n y=> steer (D' n p) d ((D' n p).atmos w) (U n y)):=by
    refine Frill.stocks fun i=>?_; let L: G.Color:=(D 0 p).atmos w i
    refine (skipper (K:=K) (H:=H) (Z:=Z) he hA i).fares (Q:=fun X:G.Mat=> fleece G Z.χ d X L) fun g hg=>?_
    have ht:=hA.side; obtain rfl : g=1:= tendsto_nhds_unique hg (by simp [Silica.action,paints] <;> exact tendsto_const_nhds)
    refine contDiffAt_const.add ?_; exact ((Eider.sheen hA Z.χ L _ (by simp [ht.le])).of_le (show (j:WithTop ℕ∞) ≤ ∞ from by exact WithTop.coe_le_coe.mpr le_top)).comp 1 (f:=fun x=> (x,L)) (contDiffAt_id.prodMk contDiffAt_const)
include h ht H₀ hz hQ
local notation "Y"=> fun n=> kickback (D n p) (K n).beta
local notation "Y'"=> fun n=> kickback (D' n p) (H n).beta
omit hA in
lemma restart (w:Air f G): Frill J j p (fun n _=> Y n w) (fun n _=> Y' n w):=by
    have hc:= (levied H₀ hQ hz h he ht).crest
    let L:Directions G f:= ((D 0 p).atmos w)
    have hS:= (Frill.bare (ticks H₀ h) (n:=j) (x:=p)).fee ((Frill.still L).sub (Frill.bare hc))
    exact aimed fun ⟨i,k⟩=> pointed (hS.cross i) k
include T
lemma sea (w:Air f G): Frill J j p (fun n y=> course (D n p) d (K n).beta (Y n w) (U n y)) (fun n y=> course (D' n p) d (H n).beta (Y' n w) (U n y)):=by
    unfold course
    simp_rw [show ∀ n,worldZ (D n p) (K n).beta (Y n w)=_ from fun n=>kickback_home _ (H₀ n).laws.intake.positive _,show ∀ n,worldZ (D' n p) (H n).beta (Y' n w)=_ from fun n=> kickback_home _ (T n).laws.intake.positive _]; let A :=d
    have hu:= (Frill.bare (ticks H₀ h)).fee ((skipperY (K:=K) (H:=H) (Z:=Z) he hA w).sub (levied H₀ hQ hz h he ht)); refine aimed fun ⟨i,k⟩=>?_ ; exact pointed (hu.cross i) k
lemma summer (w:Air f G)(I:Finset (Bond f)): Frill J j p (fun n y=> jacL I (D n p) d (K n).beta (U n y) (Y n w)) (fun n y=> jacL I (D' n p) d (H n).beta (U n y) (Y' n w)):=by
     unfold jacL; simp_rw [show ∀ n, worldZ (D n p) (K n).beta (Y n w)= _ from fun n=> kickback_home _ (H₀ n).laws.intake.positive _, show ∀ n, worldZ (D' n p) (H n).beta (Y' n w)= _ from fun n=> kickback_home _ (T n).laws.intake.positive _]; exact Frill.pears _ fun i _=> skipJ (Z:=Z) (K:=K) (H:=H) he hA w i
abbrev rho (I:Finset (Bond f))(M:Matrix (Tubular f G) (Tubular f G) ℝ)(w:Air f G):= lens₀ (Pond.circuit (lensS I G) M) (swim _ w)
omit T hA in
private lemma cardxp (I:Finset (Bond f)){s t:ℕ→ E→ Air f G}(hv:Frill J j p s t): Frill J j p (fun n y=> rho I (D n y|>.relating) (s n y)) (fun n y=> rho I (D' n y|>.relating) (t n y)) ∧ ∀ l,Tendsto (fun n=> rho I (D n p|>.relating) (s n p)) J (𝓝 l)→ 0<l:=by
    let W':=lensS I G
    let f(n:ℕ)(y:E):= Pond.circuit W' (D n y|>.relating); let g(n:ℕ)(y:E):=Pond.circuit W' (D' n y|>.relating);
    have hk: Buds J j p f g:= (relate H₀ hz h (scaleG he) ht).below Subtype.val
    have hh : ∀ᶠ n in (J:Filter ℕ), Allow (f n p) (Census.along S ∘ Subtype.val) (Census.tubularPrice G L) _ _ _:= ht.mono fun i hi=> own_mat ((H₀ i).laws.data.localP F (D i p) hz.1 hz.2 hi).sails I
    exact lensP hh hk (u:=fun n y=> swim W' (s n y)) (w:=fun n y=> swim W' (t n y)) (aimed fun k=>pointed hv k.val)
omit T hA in
private lemma share (w:Air f G)(I:Finset (Bond f)): Frill J j p (fun n _=> (rho I (D n p|>.relating) (Y n w))⁻¹) (fun n _=> (rho I (D' n p|>.relating) (Y' n w))⁻¹):=by
    obtain ⟨hz,hY⟩:= cardxp H₀ hQ hz h he ht I (restart H₀ hQ hz h he ht w)
    exact Frill.bare ((hz.crest).bin (Q:=fun x:ℝ=>x⁻¹) (fun i hi=> continuousAt_inv₀ (hY i hi|>.ne')))
lemma ship (w:Air f G)(I:Finset (Bond f)): Frill J j p (fun n y=> scalp I (D n p) (U n y) (K n).beta d (Y n w)) (fun n y=> scalp I (D' n p) (U n y) (H n).beta d (Y' n w)):=by
    have hk:= (cardxp H₀ hQ hz h he ht I (sea H₀ T hQ hz h he ht hA w)).1
    have ht:=(summer H₀ T hQ hz h he ht hA w I).times (hk.times (share H₀ hQ hz h he ht w I))
    unfold scalp; dsimp only; simp_rw [div_eq_mul_inv]; exact ht
end Draft
end YM.ConnectedActivityE6.Lim
