import YM.RemainderComparison.WickReps.Quarry
import YM.RemainderComparison.Solos.Font
/-!
# Multilinear continuation *as represented* across closed analytic zones

Keys keep every (also packed test) root. A single law over all unit choices.
Indicator restoration requires linearity of unmasked germs ALSO near
boundary; extension elsewhere is performed without requiring equality there
on an uninspected germ.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Solos
open Function Filter Finset Lattice RG Wilson MeasureTheory
open Push Push.AbsoluteSums WickReps Flues Scone
open Mosaic
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {θ ι : Type} {R₀ : θ→Type*} [∀ i, NormedAddCommGroup (R₀ i)] [∀ i,NormedSpace ℝ (R₀ i)]
variable {J:Type} {G:Gauge}{c:Side}
variable (P:BudgetPoint)(S:Support c)(U V : Config G c)(f:Config G c→Prop)
-- Local interior.S.Cliff
lemma roomier (h:∀ X Y:Config G c,Agrees S X Y→ f X=f Y)(he:Agrees S U V) (hf:∀ᶠ x in 𝓝 U,f x) : ∀ᶠ x in 𝓝 V, f x:=by
   let W (x:Config G c) : Config G c := fun e=> x e * ((V e)⁻¹*U e)
   have hp: W V=U :=by ext; simp [W]; -- edit
   have hw (x:Config G c): Agrees S (W x) x:= fun i hi hh=> (by unfold W; rw [he i hi hh, inv_mul_cancel,mul_one])
   have hk : Tendsto W (𝓝 V) (𝓝 U) :=by nth_rw 1 [← hp]; apply Continuous.tendsto; unfold W; fun_prop
   exact (hk.eventually hf).mono (fun x hx=> (h _ _ (hw x)) ▸ hx)
lemma usual (k:Site c→G.El) (h:∀ U V,f (Lattice.gauge U V)=f V) (hf:∀ᶠ x in 𝓝 U,f x): ∀ᶠ x in 𝓝 (Lattice.gauge k U), f x:=by
   have he : Lattice.gauge k⁻¹ (Lattice.gauge k U)=U:=by ext; simp [Lattice.gauge,mul_assoc]
   have ht : Tendsto (Lattice.gauge k⁻¹) (𝓝 (Lattice.gauge k U)) (𝓝 U):= by obtain hK : Tendsto (Lattice.gauge k⁻¹) (𝓝 (Lattice.gauge k U)) (𝓝 (Lattice.gauge k⁻¹ (Lattice.gauge k U))) := (show Tendsto _ _ (𝓝 (Lattice.gauge k⁻¹ (Lattice.gauge k U))) from Continuous.tendsto (by unfold Lattice.gauge; fun_prop) _); rw [he] at hK; exact hK
   exact (ht.eventually hf).mono (fun x hX=> h k⁻¹ x ▸ hX)
variable (Φ:Audited R₀→ Config G c→ℝ)(p:Finset θ)
def promise := interior {v| LinearP p fun i=> Φ i v}
def lyric (x:Audited R₀):Config G c→ℝ := Set.indicator (promise Φ p) (Φ x)
local notation "X"=> promise Φ p
variable (hv:∀ x,P.Regular S (Φ x)) (u:Audited R₀)
include hv
lemma promise_reads (h: Agrees S U V) : U∈ X ↔ V∈ X :=by
    have hv x y (h:Agrees S x y) : (fun u=> Φ u x)=(fun u=>Φ u y):= funext fun u=> (hv u).sites x y h
    let f v:= LinearP p fun i=> Φ i v; have hh (x y)(h:Agrees S x y): f x=f y:= congr_arg (LinearP p) (hv _ _ h)
    simp_rw [promise,mem_interior_iff_mem_nhds]; exact ⟨roomier S U V f hh h,roomier S V U f hh fun e he hk=> (h e he hk).symm⟩
lemma promise_halos (k:Site c→ G.El) : Lattice.gauge k U∈ X ↔ U∈ X:=by
    have hv k U: (fun u=> Φ u (Lattice.gauge k U))=(fun u=> Φ u U):= funext fun u=> (hv u).symmetry k U
    let f v:= LinearP p fun i=> Φ i v; have hh(k U) : f (Lattice.gauge k U)= f U:= congr_arg (LinearP p) (hv k U)
    simp_rw [promise,mem_interior_iff_mem_nhds]; have he : Lattice.gauge k⁻¹ (Lattice.gauge k U)=U:=by ext; simp [Lattice.gauge,mul_assoc]
    exact ⟨fun H:∀ᶠ x in 𝓝 _, f x=> he ▸ (usual (Lattice.gauge k U) f k⁻¹ hh H),usual U f k hh⟩
omit hv
-- Family in linear basis.Mode extraction after
lemma growth (x:Config G c) : LinearP p fun b=> lyric Φ p b x:=by
    unfold lyric; by_cases h:x∈ X
    · simp_rw [Set.indicator_of_mem h]; exact (show x ∈ {v| LinearP p fun i=> Φ i v} from interior_subset h)
    simp_rw [Set.indicator_of_notMem h]; exact LinearP.nil _
variable (h : ∀ U,Healthy P.threshold S U→∀ᶠ z in 𝓝 U,LinearP p fun i=> Φ i z)
include h
lemma sung (hp:Healthy P.threshold S U): lyric Φ p u=ᶠ[𝓝 U] Φ u:= (show ∀ᶠ x in 𝓝 U,x∈ X from isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr (show {v| LinearP p fun i=> Φ i v} ∈ 𝓝 U from h U hp))).mono fun _ hi=>Set.indicator_of_mem hi _
include hv
lemma epode : P.Regular S (lyric Φ p u):=by
    have hh(U:Config G c)(H:Healthy P.threshold S U) : Push.Local.Chart P.order (lyric Φ p u) U:=by
       apply ContDiffAt.congr_of_eventuallyEq (f:= Φ u ∘ increment U) (hv u|>.smooth U H); apply (sung P S U Φ p u h H).comp_tendsto (by simpa only [Work.G07.at_zero_increment] using! (show Continuous (increment U) from by unfold increment; fun_prop).tendsto 0)
    refine ⟨?_, ((hv u).borel.indicator isOpen_interior.measurableSet), ?_,hh,fun U H A l hl=> Next.Foundations.left_has _ hl (hh U H)⟩ -- finder
    · intro U V h; unfold lyric Set.indicator; simp_rw [promise_reads P S U V Φ p hv h]; rw [(hv u).sites U V h]
    · intro k U; unfold lyric Set.indicator; simp_rw [promise_halos P S U Φ p hv]; rw [(hv u).symmetry k U]
omit hv
lemma poet {B:ℝ} {o:Site c} (hh:P.supBounds o S (Φ u) B) : P.supBounds o S (lyric Φ p u) B:=by
    refine ⟨hh.1,fun U hu l hl hf=> ?_⟩; rw [(UVNext.PricedKernels.left_congr (sung P S U Φ p u h hu) l).self_of_nhds]; exact hh.2 U hu l hl hf
end YM.RemainderComparison.Solos
