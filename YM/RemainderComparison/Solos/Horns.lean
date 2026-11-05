import YM.RemainderComparison.Solos.Hues
import YM.RemainderComparison.Ethereal.Models
/-!
# Loyalty to test address markings
 Needed only for uniform integrability near equality F.B.Flags. For all other uses
 preserve the real rendered leaves. `weight` is before probe restriction.
 Honors support, gauges and flags. Don't require a cost summable over tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Solos
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {θ ι : Type} {R₀ : θ→Type*} [∀ i, NormedAddCommGroup (R₀ i)] [∀ i,NormedSpace ℝ (R₀ i)]
variable {α:Type*}{G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic Sleet Serif Typeface
variable (M:ι→Portrait R α) (y:α)
-- place : all tags of leaf (empty if dormant)
variable (M:ι→Portrait R (Audited R₀)) (place :ι→ Finset θ)(Hpc: ∀ (U:Config G f) i, LinearP (place i) (fun a=> ((brand M a i).ingredient U)))
local notation "V'" z:max=> brand M z
open Mosaic.Verse Lacuna Lobby WickReps Lobby.Vesuvius Jolt Flues Progress.DirectedRecipe
variable {I J : Type} {Z:Set ι}(a':Audited R₀)
local notation "E" => Audited R₀
-- all-countable Mark with support roots. Data-aware over independent θ tests,
-- when repeated inputs are present one particular label may still be meaningful if its θ tag was *not* charged. Precisely supply inactive θ for dormant leaves, and only nilpotent contributes positive load.
variable (Z:Set ι)
structure Articles (place :ι→ Finset θ) : Prop where
   used : ∀ i, i∈Z ↔ (place i).Nonempty
local notation "l'"=> mapWord place
lemma Articles.law (p:Multiset ι) (h:Articles Z place) : Verse.load Z p=0↔ mapWord place p=0:= by -- argument order!
    induction p using Multiset.induction_on with
    | empty=> simp [Verse.load]
    | cons i p hp=>
        rw [show l' (i ::ₘ p)=_ from congr_arg (⇑l') (Multiset.singleton_add i p).symm, map_add]
        have he: l' ({i}:Multiset ι)=(place i).val:=by simp [mapWord]
        rw [he]; by_cases hi:i∈ Z
        · have hv : (place i).val≠0:=by simpa using Finset.nonempty_iff_ne_empty.mp (h.used i |>.mp hi)
          simp [Verse.load,hi,hv]
        have hv : place i=∅:=Finset.not_nonempty_iff_eq_empty.mp (mt (h.used i|>.mpr) hi)
        unfold Verse.load at hp ⊢; simpa [hi,hv] using hp

variable (Bv:Yard ι (Audited R₀) G c) (L': Vesuvius G c ι I (Audited R₀))(L: Scone ι (Audited R₀) G c)
structure Volta (D:Yard ι (Audited R₀) G c) : Prop where
   crest i (U:Config G c) : PaperP (mapWord place (D.score i)) (fun b=>D.glow b i U)
structure Hearth (D:Vesuvius G c ι I (Audited R₀)) : Prop where
   touch i : Verse.load Z (D.opus i) ≠ 0 →∀ U,PaperP (mapWord place (D.opus i)) (fun b=>D.log b i U)
structure Sugar (D:Scone ι (Audited R₀) G c) : Prop where
   rings i (U:Config G c) : PaperP (mapWord place (D.glyph i)) (fun b=> D.glow b i U)
variable {place Z Bv L L'}
lemma Hearth.burns [Countable I](hp:Hearth place Z L'): Sugar place (Lacuna.rudder L' Z a'):=by
    let D:=bubbles L' Z a'; have hx i U : PaperP (l' (D.opus i)) (fun b=>D.log b i U):=by
       obtain ⟨x,i⟩:=i; unfold D bubbles; by_cases hi : i ∈ Lacuna.shade L' Z
       · simp only [if_pos hi,map_zero]; intro h; rw [Multiset.toFinset_zero]; apply LinearP.buoy
       by_cases h:x=Jolt.standing c
       · subst x; simp only [if_neg hi,↓reduceIte]; exact hp.touch i hi U
       simp only [if_neg hi,if_neg h]; exact fun _=> LinearP.nil _
    constructor; intro i U; unfold rudder; by_cases hi:i∈ Set.range (Lacuna.plugs c (I:=I))
    · obtain ⟨j,rfl⟩:=hi; simp_rw [stuffed]; exact hx j U
    dsimp only; simp_rw [Progress.DirectedRecipe.blank _ _ hi]; exact fun _=> LinearP.nil _
open Ethereal
lemma Sugar.crisp {D:Scone ι (Audited R₀) G c} (hp:Sugar place L)(hv:Sugar place D): Sugar place (Ethereal.blend L D):=by
    constructor; intro i U; unfold blend; dsimp only [Function.comp_apply]; cases Ethereal.stem i
    · exact hp.rings _ U
    exact hv.rings _ U
lemma bouquet (L :Hiss G c) : Sugar place (L.twig : Scone ι (Audited R₀) G c) := by
    constructor; intro i U; unfold Hiss.twig; dsimp only; rw [map_zero]; intro h; simp; apply LinearP.buoy

lemma Voltage {D : Yard ι (Audited R₀) G c} {f:ℕ↪ℕ} (hp:Jolt.Padded Bv D f)(hh: Volta place Bv): Volta place D:=by
    constructor; intro i U; by_cases hi:i∈Set.range f
    · obtain ⟨j,rfl⟩:=hi; simp_rw [hp.labels,hp.amount]; exact hh.crest j U
    simp_rw [hp.cleared i hi]; exact fun _=> LinearP.nil _
lemma lava (hv:Articles Z place)(hp:Sugar place L)(hh:Volta place Bv)(P:BudgetPoint)(F: ℕ≃ (Flues.fireplace Bv L).Pellet): Volta place (Flues.flash Bv L P Z F) :=by
    constructor; intro i U; unfold Flues.flash; dsimp only; split_ifs
    next h=>
       rw [map_sum]; refine PaperP.stack _ _ _ fun j _=> ?_; rcases j with j|j; exact hh.crest j U
       change PaperP (l' (L.glyph j)) (fun v=> Scone.tinct L Z v j U)
       unfold Scone.tinct; split_ifs; next hj=>
         have hk := (Articles.law place Z (L.glyph j) hv).1 hj; have he:= hp.rings j U; rw [hk] at he ⊢
         intro h'; rw [Multiset.toFinset_zero]; have ht:=he h'; rw [Multiset.toFinset_zero] at ht
         have hv (a:Audited R₀) : L.glow a j U=L.glow (Classical.ofNonempty :Audited R₀) j U:= ht.tune ..
         have hl : (fun v:Audited R₀=> Real.exp (L.glow v j U)-1)=fun _=> Real.exp (L.glow (Classical.ofNonempty) j U)-1:=funext fun i=> congr_arg (fun x=>Real.exp x-1) (hv i)
         rw [hl]; exact LinearP.buoy _
       next=> exact hp.rings j U
    next=> exact fun _=> LinearP.nil _
variable {L : Vesuvius G c ι I (Audited R₀)}
lemma starlet [Countable I] (hA:Articles Z place)(hp:Hearth place Z L)(hh:Volta place Bv){T:Manor G c ι (Audited R₀) J} [Countable J] (F:Posture G c ℕ) (W: PathData G)(B: Clip)(P:BudgetPoint): Volta place (Ethereal.dawnG F Bv T L P Z a' W B):=
    lava hA ((Hearth.burns a' hp).crisp ((bouquet F.hue).crisp (bouquet _))) hh _ _
-- Edit name/title ReaderPin habitat
end YM.RemainderComparison.Solos
