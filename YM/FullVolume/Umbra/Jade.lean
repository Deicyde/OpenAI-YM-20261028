import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Reseve
import YM.FullVolume.Umbra.Tome
import YM.FullVolume.Renew.Ready
-- one real mark among any two epoch carpets at the same stamp
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
namespace Umbra
namespace Jade
variable {ι θ:Type}
lemma freeze {F G':ℕ→ι→ Config G c→ℝ}(h:Angel F G') : Jade (fun n _=>F n) (fun n _=>G' n):=by
   have hp(F:ℕ→ι→ Config G c→ℝ)(h:Vented F):Back fun n _=>F n:=by
        obtain ⟨u,hu,H⟩:= h.sup; exact ⟨_,hu,fun n i v=>⟨differentiableAt_const _,by simpa only [Real.norm_eq_abs, deriv_const,abs_zero,add_zero] using H n v i⟩⟩
   exact ⟨hp _ h.a,hp _ h.b,fun i V J hx=> Steps.constant (h.glints hx i V)⟩
variable {F G':Tilt ι G c}
lemma extendsJ (h:Jade F G')(i:ι↪θ):Jade (fun n x=>stuff i (F n x)) (fun n x=>stuff i (G' n x)):=by
   have hx(F:Tilt ι G c)(h:Back F):Back fun n x=>stuff i (F n x):=by
       obtain ⟨w,hw,H⟩:=h.bins; refine ⟨_,Ledgers.hopper hw i,fun n p V=>?_⟩; by_cases he:p∈Set.range i
       · obtain ⟨p,rfl⟩:= he; simp_rw [stuffed]; exact H ..
       simp_rw [blank _ _ he]; exact price_zero
   refine ⟨hx _ h.a,hx _ h.b,fun p V J hj=>?_⟩; by_cases he:p∈ Set.range i
   · obtain ⟨p,rfl⟩:=he; simp_rw [stuffed]; exact h.converge p V J hj
   simp_rw [blank _ _ he]; exact Steps.constJ (0:ℝ)
lemma pullJ (h:Jade F G')(i:θ↪ι): Jade (fun n x p=> F n x (i p)) (fun n x p=> G' n x (i p)):=by obtain ⟨a,ha,H⟩:=h.a.bins; obtain ⟨b,hb,F⟩:=h.b.bins; exact ⟨⟨_,ha.pull i,fun j p V=>H ..⟩,⟨_,hb.pull i,fun j p V=> F ..⟩,fun p=> h.converge _⟩
lemma plus {F G':Tilt (ι⊕θ) G c} (h:Jade (fun n x k=>F n x (.inl k)) (fun n x k=> G' n x (.inl k)))(hp:Jade (fun n x k=>F n x (.inr k)) (fun n x k=> G' n x (.inr k))): Jade F G':=by
    have hf(F:Tilt (ι⊕θ) G c)(h:Back fun n x k=> F n x (.inl k))(hp:Back fun n x k=> F n x (.inr k)): Back F:=by obtain ⟨a,ha,hA⟩:=h.bins; obtain ⟨b,hb,hB⟩:= hp.bins; refine ⟨fun i=>Sum.elim (a i) (b i),Sparse.either ha hb,fun n p V=>?_⟩; cases p <;> first|exact hA ..|exact hB ..
    exact ⟨hf _ h.a hp.a,hf _ h.b hp.b,fun x V J he=> by cases x <;>first|exact h.converge _ V J he|exact hp.converge _ V J he⟩
open Pipes
lemma spins {U V:ℕ→ℝ→ Tap G c} {E:Pipes G c}(X:ℕ≃ E.Pellet) (h:Jade (fun n x=> reach (U n x)) (fun n x=> reach (V n x)))(P:BudgetPoint): Jade (fun n x=> solid X P (U n x)) (fun n x=>solid X P (V n x)):=by
   let k:= X.toEmbedding.trans (Embedding.subtype _)
   have hp {F:ℕ→ℝ→ Tap G c}(h:Back fun n x=> reach (F n x)):Back fun n x=>solid X P (F n x):=by
       obtain ⟨v,hv,H⟩:=h.bins; have hk := hv.arbitrary.pull k; refine ⟨_,hk,fun n p z=>?_⟩; unfold Pipes.solid;split; next he=> exact carryJ (g:=fun l x=>reach (F n x) l z) _ fun i=> H n i z
       next he=> exact climbing price_zero (hk.value ..)
   refine ⟨hp h.a,hp h.b,fun i V' J hj=>?_⟩; unfold Pipes.solid
   -- class issue Decidable inherited
   exact Steps.switchJ (Steps.product (f:=fun i n x=> reach (U n x) i (V' n)) (g:=fun i n x=> reach (V n x) i (V' n)) _ (fun i=> h.converge i V' J hj)) (fun n=> (addr X P i).eligible P.threshold (V' n))
open Rack Mallow
lemma sailed {U U':Tilt ℕ G c}(ht:Jade U U') {X Y:ℕ→ Tap G c}(hv:Angel (fun n=> (X n).logarithm) (fun n=> (Y n).logarithm))(P:BudgetPoint){A: Pipes G c}(E:ℕ≃ A.Pellet): Jade (fun n x=>solid E P (spice (X n) (U n x))) (fun n x=>solid E P (spice (Y n) (U' n x))):= spins (U:=fun n x=> spice (X n) (U n x)) (V:=fun n x=> spice (Y n) (U' n x)) E (Jade.plus ht (freeze hv.rings)) P
lemma answer {U U':Tilt ℕ G c}(ht:Jade U U') {X Y:ℕ→ Tap G c}(hv:Angel (fun n=>(X n).logarithm) (fun n=>(Y n).logarithm))(P:BudgetPoint)(A:Pipes G c): Jade (fun n x=> final.frigid A (X n) (U n) P x) (fun n x=>final.frigid A (Y n) (U' n) P x):=by
    have hp:Angel (fun n=> (widen A (X n)).logarithm) (fun n=> (widen A (Y n)).logarithm):=by
       -- ext through stuff
       obtain ⟨a,ha,hX⟩:= hv.a.sup; obtain ⟨b,hb,hY⟩:=hv.b.sup; let e:= upS A
       have hs : Jade (fun n _x=>stuff e (X n).logarithm) (fun n _x=> stuff e (Y n).logarithm):= (freeze hv|>.extendsJ e)
       obtain ⟨a,hA,hU⟩:= hs.a.bins; obtain ⟨d,hD,hW⟩:= hs.b.bins
       refine ⟨⟨_, hA,fun n V i=> ?_⟩, ⟨_,hD,fun n V i=>?_⟩,fun i b ht=> recover (fun V=> (tendsto_iff_ultrafilter ..).mpr fun J hj=> (hs.converge i V J hj).value.shrank) b ht⟩
       · have he : ‖(widen A (X n)).logarithm i V‖ ≤ a n i:= (le_add_of_nonneg_right (abs_nonneg _)).trans (hU n i V).2; exact he -- verify target
       exact (le_add_of_nonneg_right (abs_nonneg _)).trans (hW n i V).2
    exact sailed (ht.extendsJ (upK A)) hp P _
lemma cusp (h:Jade F G') : Angel (fun n i V=>deriv (fun x=>F n x i V) 0) (fun n i V=>deriv (fun x=>G' n x i V) 0):=by
    obtain ⟨a,hA,H⟩:=h.a.bins; obtain ⟨b,hB,h'⟩:=h.b.bins
    exact ⟨⟨_,hA,fun n V i=> (le_add_of_nonneg_left (abs_nonneg _)).trans (H n i V).2⟩,⟨_,hB,fun n V i=> (le_add_of_nonneg_left (abs_nonneg _)).trans (h' n i V).2⟩,fun i a hA=> recover (fun V=> (tendsto_iff_ultrafilter ..).mpr fun J hj=> (h.converge i V J hj|>.roofs.shrank)) _ hA⟩
end Jade
end Umbra
end YM.ConnectedActivityE6.Lim
