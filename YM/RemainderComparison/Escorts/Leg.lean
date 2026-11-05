import YM.RemainderComparison.Escorts.Reel
import YM.RemainderComparison.Placement.Pose
/-! # Tilt leaks for unmasked actual Countable-log presentation
    each new marked lift on own slot ONLY. False posture labels in library
    remain fully present for orbit but have zero payload.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Escorts
open Function Filter Finset Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Push Push.AbsoluteSums PhysicalNext.Repeat
open Merge Mosaic Mosaic.Verse Marker Jolt Flues Placement Progress.DirectedRecipe Animals
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c:Side}{ι κ:Type}{α:Type*}
variable {I:Type} [Countable I]{q e:ℕ}{A:ℝ}
variable (T:I→Tile G α q e A) (a:α) (p:BudgetPoint)(o:I→Site c)
local notation "v" x:max=> (neighbors e x)
set_option quotPrecheck false
local notation "ζ"=> Placement.numbers I c

def jet : I ↪ ℕ:=⟨fun i=> (ζ).symm (.inr (o i,i)),fun _ _ h=>congr_arg Prod.snd (Sum.inr_injective ((ζ).symm.injective h))⟩
local notation "ε"=> Escorts.jet o

def leak (i:I)(V:Config G c):= Tile.read (T i) (o i) a V - RG.masked p.threshold (neighbors e (o i)) (Tile.read (T i) (o i) a) V

def tinge : Scone I α G c:=
    ⟨(Sum.elim (fun _=> Finset.univ) (fun i:Site c×I=>neighbors e i.1)) ∘ ζ,
     by
       intro i; simp only [Function.comp_apply]; rcases he: ζ i with i|⟨x,i⟩; exact univ_nonempty
       exact ⟨x,(neighbors_mem ..).mpr (by rw [separation_self]; omega)⟩,
     (Sum.elim (fun _=> 0) (fun i:Site c×I=>{i.2})) ∘ ζ,
     fun a=>stuff ε (Escorts.leak T a p o)⟩
local notation "S" => tinge T p o
local notation "u"=> (Set.univ:Set I)
local notation "ρ"=> fun i:I=> neighbors e (o i)

lemma axle (i) : (S).leg (ε i)=ρ i ∧ (S).glyph (ε i)={i}:=by unfold tinge; dsimp only [Function.comp_apply]; rw [show ε i=(ζ).symm _ from rfl,Equiv.apply_symm_apply]; exact ⟨rfl,rfl⟩
lemma ascends (i) : ¬ dawn S u (ε i):=by unfold dawn; rw [(axle T p o i).2]; simp [Verse.load]
lemma leaking (i) : (S).glow a (ε i)= Escorts.leak T a p o i:= stuffed ..
lemma chalk i : Jolt.dawn S u i→∀ b,(S).glow b i=0:=by
   intro h b; refine blank _ _ ?_; rintro ⟨j,rfl⟩; exact Escorts.ascends T p o _ h
lemma uplands : Scone.Rises S p (fun i=>neighbors e (o i)):=by
   have hU i b: UsesFinal p.threshold ((S).leg i) ((S).glow b i)∧ Measurable ((S).glow b i) ∧ GaugeInvariant ((S).glow b i)∧ (apex (ρ) ((S).leg i) ((S).glyph i) ((S).glow b i))∧ ∀ V,Healthy p.threshold ((S).leg i) V→ (S).glow b i V=0:=by
       by_cases he:i∈ Set.range ε
       · obtain ⟨j,rfl⟩:=he; let x:=o j; let Y:=neighbors e x
         have hp:= Extra.Iteration.Derivs.canonical_regular ((T j).stamp b) x p ((T j).gauge b)
         have hs: LocalOn (Y:Set _) (Tile.read (T j) x b):= fun U V h=> hp.sites U V (agrees_mono h (Tile.reach ..))
         rw [(axle T p o j).1,(axle T p o j).2,leaking]; unfold leak
         refine ⟨?_,?_,?_,?_,?_⟩
         · intro U V h ht; have he : Healthy p.threshold Y U ↔ Healthy p.threshold Y V:=by unfold Healthy; rw [Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_iff_inter_eq_empty, show Y∩flags _ U= _ from ht]
           dsimp only; rw [hs _ _ h]; by_cases hn : Healthy p.threshold Y U
           · rw [masked_eq _ _ _ _ hn,masked_eq _ _ _ _ (he.mp hn),hs _ _ h]
           rw [masked_ne _ _ _ _ hn,masked_ne _ _ _ _ (mt he.mpr hn)]
         · let f:= Tile.read (T j) x b; have hf: Measurable f:=hp.borel; exact hf.sub (masked_measurable _ _ _ hf)
         · intro k V; have hp : GaugeInvariant (Tile.read (T j) x b):= hp.symmetry
           have he : Healthy p.threshold Y (gauge k V) ↔ Healthy p.threshold Y V:=by unfold Healthy; rw [gauge_flags]
           have hx: Tile.read (T j) (o j) b (gauge k V)= _:= hp k V
           dsimp only; rw [hx]; by_cases hn : Healthy p.threshold Y V
           · rw [masked_eq _ _ _ _ (he.mpr hn),masked_eq _ _ _ _ hn,hx]
           rw [masked_ne _ _ _ _ (mt he.mp hn),masked_ne _ _ _ _ hn]
         · intro i hi; have hh:= Multiset.mem_singleton.mp hi; subst i; exact fun _ _=>Subset.rfl
         intro V hV; rw [masked_eq _ _ _ _ hV,sub_self]
       rw [show (S).glow b i=0 from Progress.DirectedRecipe.blank _ _ he]
       exact ⟨fun _ _ _ _=>rfl,measurable_const,fun _ _=>rfl,fun _ _ _ hn=> (hn rfl).elim,fun _ _=>rfl⟩
   exact ⟨fun a i=>(hU i a).1,fun a i=>(hU i a).2.1,fun a i=> (hU i a).2.2.1,fun i a=>(hU i a).2.2.2.1,fun i a=> (hU i a).2.2.2.2⟩
lemma breeze : Jolt.Whirls S u:=by
    refine ⟨fun i h a b=> (chalk T p o i h a).trans (chalk T p o i h b).symm,fun s t=>?_⟩
    let d:= Equiv.sumCongr (Equiv.refl ℕ) (Placement.perm I s t); let f:= ((ζ).trans d).trans (ζ).symm
    have hp i: ζ (f i)=d (ζ i):= (ζ).apply_symm_apply _
    have hx i: (S).glyph (f i)=(S).glyph i:= by unfold tinge; dsimp only [Function.comp_apply]; rw [hp]; cases hh:ζ i<;> rfl
    refine ⟨f,fun i=> ⟨by unfold dawn; rw [hx],?_ ,?_⟩⟩
    · unfold tinge; dsimp only [Function.comp_apply]; rw [hp]; rcases hi:ζ i with i|⟨x,i⟩
      · ext x; change x∈ (Finset.univ:Support c)↔ x∈ Finset.univ.image _; obtain ⟨j,hj⟩:= (StepData.sendSites s t).surjective x; exact ⟨fun _=>Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩,fun _=> Finset.mem_univ x⟩
      exact Turn.circle_wind s t x e
    intro h V a; rw [chalk T p o i h a, chalk T p o (f i) (by unfold dawn; rw [hx]; exact h) a]; rfl
end YM.RemainderComparison.Escorts
