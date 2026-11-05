import YM.FullVolume.E6.Jag
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
section bridges
variable {P0:Type} [MeasurableSpace P0] {μ : Measure P0}
lemma crush {B:ℕ→P0→E}{v:P0→ℝ}(h:Integrable v μ) (he:∀ i,Integrable (B i) μ)(hx:∀ i, ∀ᵐ p∂μ,‖B i p‖ ≤ v p)(hf:∀ᵐ p∂μ,Tendsto (fun i=> B i p) atTop (𝓝 0)): Tendsto (fun i=>∫ p, B i p ∂μ) atTop (𝓝 0):=by
    simpa using tendsto_integral_of_dominated_convergence (f:=fun _=> (0:E)) v (fun i=> (he i).aestronglyMeasurable) h hx hf -- order
end bridges
variable (X:∀ n,Coat (K n).tubes F)(Y:∀ n,Coat (H n).tubes F)(I:Depot Q o x μ L C₀ K) (T:Depot Q o x μ L C₀ H)
set_option quotPrecheck false
local notation "B"=> F.order G
local notation "∇"=> fun n=> (F.order G).prod (X n).dice
local notation "Δ"=> fun n=> (F.order G).prod (Y n).dice
abbrev Lumen (F:Forest S.ratio)(G:Gauge)(E:Type):= ℕ→ F.Slice G × Air f G→ E
abbrev footZ (X:∀ n,Coat (K n).tubes F)(A:Lumen F G E)(n:ℕ)(Y:F.Slice G)(w:Air f G):E:= cups ((X n).wrapY Y) (K n).beta w • A n (Y,kickback ((X n).wrapY Y) (K n).beta w)
structure Spunky (x:ℝ)(o:Target.Order G W)(X:∀ n,Coat (K n).tubes F):Prop where
    volt:∀ n,(X n).x=x
    width:∀ n,(X n).width=o.K
    valid:∀ n,(X n).manifest
structure Peaking (X:∀ n,Coat (K n).tubes F)(A:Lumen F G E):Prop where
    use n:Integrable (A n) ((F.order G).prod (X n).dice)
    cost : ∃ D: Finset (Bond f),∃ p:ℕ, ∃ C:ℝ,0≤C ∧ ∀ n y z, ‖A n (y,z)‖≤ C*facescale D z^p
variable {X Y} {A C:Lumen F G E}
namespace Peaking
variable (h:Peaking X A)(hx:Spunky x o X)
include h hx I
lemma needed : ∃ D:Air f G→ℝ, Integrable D ∧ ∀ n y w, ‖footZ X A n y w‖ ≤ D w := by
    obtain ⟨D,k,C,hC,he⟩:= h.cost; obtain ⟨P,hr,hP,hK⟩:= impartial I X hx.volt hx.width hx.valid D k
    refine ⟨fun x=> C*P x,hP.const_mul C,fun n y w=>?_⟩
    let T:=(X n).wrapY y; let c:=cups T (K n).beta w
    let Z:= kickback T (K n).beta w; obtain ⟨hk,h⟩:=hK n y w; change 0≤c at hk
    unfold footZ; rw [norm_smul,Real.norm_of_nonneg hk]; apply (mul_le_mul_of_nonneg_left (he ..) hk).trans
    rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left h hC
abbrev rho (X:∀ n,Coat (K n).tubes F)(A:Lumen F G E)(n:ℕ) (y:F.Slice G):= ∫ z,A n (y,z) ∂(X n).dice
lemma fiscal : ∀ᵐ y∂F.order G, ∀ n, Integrable (footZ X A n y) ∧ (∫ w,footZ X A n y w) = Peaking.rho X A n y:=by
     apply ae_all_iff.mpr; intro n
     filter_upwards [((integrable_prod_iff ((h.use n).aestronglyMeasurable)).mp (h.use n)).1] with y hy
     obtain ⟨ha,hB⟩:=tollway ((X n).wrapY y) (show (X n).relating.PosDef from ((I n).laws.data.localP F (X n) (hx.volt n) (hx.width n) (hx.valid n)).sails.fullC) (show 0<(K n).beta from (I n).laws.intake.positive) _ (show Integrable (fun z=> A n (y,z)) (X n).dice from hy)
     exact ⟨ha,hB.symm⟩
include T
lemma stack [CompleteSpace E] (g:Peaking Y C)(hy:Spunky x o Y)(H':∀ y w,Tendsto (fun n=>footZ X A n y w-footZ Y C n y w) atTop (𝓝 0)): Tendsto (fun n=> (∫ x,A n x ∂(∇ n))- ∫ x,C n x ∂(Δ n)) atTop (𝓝 0):=by
    obtain ⟨D,hD,hv⟩:= needed I h hx; obtain ⟨D',hD',hk⟩:= needed T g hy
    let W n y:= Peaking.rho X A n y-Peaking.rho Y C n y; let f y w n:=footZ X A n y w-footZ Y C n y w; let s:=∫ z,D z;let t:=∫ z,D' z
    have hW n:Integrable (W n) (F.order G):= ((h.use n).integral_prod_left).sub (g.use n).integral_prod_left
    have ha : ∀ᵐ p∂B,∀ n, ‖W n p‖≤ s+t:=by
        filter_upwards [fiscal I h hx, fiscal T g hy] with p hp hq n; unfold W; rw [← (hp n).2,← (hq n).2]; refine (norm_sub_le ..).trans (add_le_add ((norm_integral_le_integral_norm _).trans (integral_mono (hp n).1.norm hD (hv n p))) ?_) -- adjust
        exact (norm_integral_le_integral_norm _).trans (integral_mono (hq n).1.norm hD' (hk n p))
    have hh : ∀ᵐ p ∂B,Tendsto (fun n=> W n p) atTop (𝓝 0):=by
        filter_upwards [fiscal I h hx,fiscal T g hy] with p hp hq
        refine (crush («B»:=fun n w=> f p w n) (μ:=volume) (hD.add hD') (fun n=> (hp n).1.sub (hq n).1) (fun i=> ae_of_all _ (fun x=> (norm_sub_le ..).trans (add_le_add (hv i p _) (hk i p _)))) (ae_of_all _ (H' p))).congr' ?_
        filter_upwards with n; unfold f W; rw [integral_sub (hp n).1 (hq n).1, (hp n).2,(hq n).2]
    refine (crush (integrable_const (s+t)) hW (ae_all_iff.mp ha) hh).congr' (Eventually.of_forall fun n=>?_)
    unfold W; dsimp only; let hQ:Integrable (Peaking.rho X A n) (F.order G):= (h.use n).integral_prod_left
    let hq:Integrable (Peaking.rho Y C n) (F.order G):= (g.use n).integral_prod_left
    rw [integral_sub hQ hq, integral_prod _ (h.use n), integral_prod _ (g.use n)]
end Peaking
end YM.ConnectedActivityE6.Lim
