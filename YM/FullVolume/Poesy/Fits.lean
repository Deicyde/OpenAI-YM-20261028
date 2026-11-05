import YM.FullVolume.Poesy.Moods
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
open Yard Slide Trio Marlin
variable {A:Stars→Side}{l z:ℕ} -- fix
variable {B:BudgetPoint} {fa ga: ℕ→∀ i:Stars, Trio.Offer G (A i)}(hd:∀ i,(A i).val=2*(l+i.val))(h:∀ i j,Loom B 0 Finset.univ (fun n=>fa n i j) (fun n=>ga n i j))(hp:l+4≤z)
include hd h hp
lemma towardsB (o:Site c)(j:Stars)(k: Site (A j)) : Loom B o (neighbors z o) (fun n=> Trio.unit hd (rip (fa n)) j k o) (fun n=> Trio.unit hd (rip (ga n)) j k o):=by
    have hn:∀ i:Site (A j), separation o (Slide.sites (pad hd j) o i)≤z:=by intro i; apply (Slide.village (w:=l+j.val) _ _ _).trans; have hj:=j.isLt; omega
    let Φ : Config G c→ Config G (A j):= shape (pad hd j) o
    have hf(f:Config G (A j)→ℝ) (hx:B.Regular Finset.univ f):B.Regular (neighbors z o) (f∘Φ):=Slide.regular _ _ hx fun i=>(neighbors_mem ..).mpr (hn i)
    let M:= (2:ℝ)^B.order*(1+(z:ℝ))^(B.power*B.order); have hm:0<M:=by unfold M; positivity
    have hg(f:Config G (A j)→ℝ) (hx:B.Regular Finset.univ f) {v :ℝ}(hs:B.supBounds 0 Finset.univ f v): B.supBounds o (neighbors z o) (f∘Φ) (M*v):=by
         refine ⟨mul_nonneg hm.le hs.1,fun V hv l hl he=>?_⟩; have h:=Slide.allFlag (pad hd j) o V (neighbors z o) (fun i=>(neighbors_mem ..).2 (hn i)) B.threshold B.threshold_pos.le hv -- signature
         have hH: Healthy B.threshold Finset.univ (Φ V):=by unfold Healthy Φ; rw [h]; simp
         exact Slide.stalled (pad hd j) o f hn l V hl he (hx.smooth _ hH) (fun j hj ht=> hs.2 _ hH j hj fun i hi=>Boulevard.tiny (ht i hi) _)
    have hx (g:ℕ→ Config G (A j)→ℝ)(h:Rich B 0 Finset.univ g): Rich B o (neighbors z o) fun k=> g k ∘ Φ:= ⟨fun i=>hf _ (h.smooth i), ⟨_,fun i=>hg _ (h.smooth i) (h.sharp.choose_spec i)⟩⟩
    have h:= (h j k).still
    refine ⟨hx _ h.a,hx _ h.b,fun i hi=>(h.gaze _ (div_pos hi hm)).mono (fun n hn=> VerifiedReset.sup_le (hg _ (VerifiedReset.reg_sub (h.a.smooth n) (h.b.smooth n)) hn) ?_)⟩; exact le_of_eq (by field_simp)
lemma partyF : Canopy B (Marlin.leap (c:=c) z) (fun n=>Trio.ornament hd (fa n)) (fun n=> Trio.ornament hd (ga n)):=by
    refine Yard.cues fun i=>?_
    have hG(j:Stars):= (Yard.Loom.tall Finset.univ (fun k _=> towardsB hd h hp i j k)).seats (Slide.ray j)
    convert! Yard.Loom.tall Finset.univ (fun k _=> hG k) using 1 <;> ext n x <;> unfold Trio.ornament Trio.beacon <;> simp only [Finset.sum_apply, Pi.smul_apply,smul_eq_mul]
lemma unearnedF (u:Site c): Solo (fun n=> Trio.unearned B hd z (Trio.rip (fa n)) u) (fun n=> Trio.unearned B hd z (Trio.rip (ga n)) u):=Solo.total Finset.univ fun j _=> (Solo.coins (Solo.total Finset.univ fun k _=> Solo.born (towardsB hd h hp (emerge hd j k u) j k)) (Slide.ray j))
end YM.ConnectedActivityE6.Lim
