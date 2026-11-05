import YM.RemainderComparison.Jolt.Pure
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Jolt
open Function Filter Finset Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Push Push.AbsoluteSums PhysicalNext.Repeat
open Merge Mosaic Mosaic.Verse Marker
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open PhysicalNext.Repeat AnalyticBridge VerifiedReset Collection Quotes
open Flues ProjectorNext.Equivariance
variable {G:Gauge}{c:Side}{I ι κ:Type}{α:Type*}
variable (H:Yard ι α G c) (S:Scone ι α G c)(u:Set ι)(P:BudgetPoint)
open Flues Progress.DirectedRecipe
-- κ.Present injections preserve all old, plus pay for zeros. No positivity requirements.

variable (Q:Yard ι α G c)(f:ℕ ↪ ℕ)
structure Padded : Prop where
     fits i : Q.more (f i)= H.more i
     labels i : Q.score (f i)=H.score i
     amount i a : Q.glow a (f i)= H.glow a i
     cleared i : i∉ Set.range f → ∀ a,Q.glow a i=0
variable (h:Jolt.Padded H Q f)
include h
lemma stocks {k b:ℕ}{σ d:ℝ}(hx:H.Pays u k b σ d):Q.Pays u k b σ d:=by
    obtain ⟨g,hg,hP,hh⟩:=hx.wages; let v:=Progress.DirectedRecipe.stuff f g; have hv : ∀ i,0≤ v i := Rack.positive f g hg
    refine ⟨v,hv,fun i=> transfer_budget f (fun i=> ?_) (fun j hj=>?_) (hP i),fun i hi a U=>?_⟩
    · unfold v Yard.plane; rw [stuffed,h.fits]
    · unfold v; rw [Progress.DirectedRecipe.blank _ _ hj]; split<;> simp
    by_cases he: i∈ Set.range f
    · obtain ⟨i,rfl⟩:=he; rw [h.labels] at hi; rw [h.amount, show v (f i)=g i from stuffed ..]; exact hh i hi a U
    rw [h.cleared i he]; simpa using hv i
lemma harbor (p: Finset ℕ)(V:Config G c)(a:α): (Q.manifest a).admissible P V (p.map f)↔ (H.manifest a).admissible P V p:=by
    unfold Activities.admissible Yard.manifest; dsimp only
    rw [mapped_biUnion f (fun i=> congr_arg ForcedAddress.inventory (h.fits i))]
    exact and_congr (paired f (fun i j=> (show Disjoint (Q.more (f i)).support (Q.more (f j)).support↔_ from by rw [h.fits,h.fits])) p) Iff.rfl
lemma revisitZ {β:Type}[DecidableEq β]{J:Marker.Census β} (a:α)(z:ι→Marker.Poly J)(V:Config G c): ∑' i,Q.gala P u z a V i= ∑' i,H.gala P u z a V i:=by
    refine Progress.DirectedRecipe.transferred_packets f (fun i=>?_) (fun i k hK ht=>?_)
    · unfold Yard.gala Photo.fronts; rw [harbor H P Q f h]; refine if_congr Iff.rfl ?_ rfl -- may simpl
      rw [prod_map]; refine prod_congr rfl fun j _=>?_ ; unfold Yard.song; rw [h.labels,h.amount]
    unfold Yard.gala Photo.fronts; split; exact prod_eq_zero hK (by unfold Yard.song; rw [h.cleared k ht]; simp)
    rfl
omit h
-- padding only needed at marked slots and seemingly zero unsupported addresses.
-- packing selected rota.Any α.
variable (E : I ↪ ℕ)
abbrev Extra : Type := {i:ℕ// i∉ Set.range E} -- name conflict YM.Extra! namespace
abbrev Diadem (c:Side):= I ⊕ (Seat c× Extra E)
local notation "F₀"=> Diadem E c
local notation "P₀"=> standing c
-- trick sum complement, all natural indices.E.toEquiv proof

def rises : ℕ→ F₀:= fun j=> if h:j∈Set.range E then Sum.inl (Classical.choose h) else Sum.inr (P₀,⟨j,h⟩)
def down : F₀→ℕ:=Sum.elim E (fun j=> j.2.1)
lemma ups (i:ℕ): down (c:=c) E (rises (c:=c) E i)=i:=by
    unfold down rises; split
    next h=> exact Classical.choose_spec h
    next=>rfl
-- prep labels.Transfer

def scope (c:Side): ℕ≃ Diadem E c:=by
    haveI : Countable I:= E.injective.countable
    haveI : Infinite (Diadem E c):=Infinite.of_injective (rises (c:=c) E) (LeftInverse.injective (ups (c:=c) E))
    exact _root_.YM.Extra.Iteration.numbering (Diadem E c)
local notation "Ω"=> scope E c

def lens (c:Side): ℕ ↪ ℕ:= (show ℕ↪ Diadem E c from ⟨rises (c:=c) E,LeftInverse.injective (ups (c:=c) E)⟩).trans (scope E c).symm.toEmbedding
local notation "Lp"=> Jolt.lens E c

def youth : F₀ → ForcedAddress G c := Sum.elim (H.more ∘ E) (fun j=> Jolt.spring (H.more j.2.1) j.1)
def clue : Yard ι α G c:= ⟨Jolt.youth H E ∘ Jolt.scope E c, H.score ∘ down (c:=c) E ∘ Jolt.scope E c,fun a=> Progress.DirectedRecipe.stuff (lens E c) (H.glow a)⟩
local notation "W₀" => clue H E
lemma leagues i : Ω (Lp i)=rises (c:=c) E i:=(Ω).apply_symm_apply _
lemma imprint : Padded H W₀ (lens E c):=by
    refine ⟨fun i=> ?_, fun i=> ?_, fun i a=> Progress.DirectedRecipe.stuffed _ _ _, fun i h a=> Progress.DirectedRecipe.blank _ _ h⟩
    · unfold clue; dsimp only [Function.comp_apply]; rw [leagues]; unfold youth rises; split; next h=> exact congr_arg H.more (Classical.choose_spec h)
      next h=> exact lock _
    unfold clue; dsimp only [Function.comp_apply]; rw [leagues,ups]
-- Shared.All
lemma pier (root:ι→Support c)(h:H.Sounds P root) : Yard.Sounds W₀ P root :=by
    have hZ i : ∀ a:α, Jolt.Placed (H.more i) P.threshold :=fun a=> ⟨fun x y=> propext ((h.families a).symtest i x y),(h.families a).meas_test i,(h.families a).reads_test i⟩
    have hf:= imprint H E; constructor
    · intro a; let F:= (W₀).manifest a; have hw i : Placed (F.forced i) P.threshold :=by
         change Placed ((Jolt.youth H E) ((Jolt.scope E c) i)) P.threshold
         cases Jolt.scope E c i with
         | inl i=> exact hZ (E i) a
         | inr i=> exact Jolt.situated (hZ _ a) i.1
      have he i : GaugeInvariant ((W₀).glow a i) ∧ Measurable ((W₀).glow a i) ∧ UsesFinal P.threshold ((W₀).more i).support ((W₀).glow a i)∧ ∀ U, (W₀).glow a i U≠0→ ((W₀).more i).eligible P.threshold U:=by
         by_cases ht:i∈Set.range (lens E c)
         · obtain ⟨i,rfl⟩:=ht; rw [hf.fits,hf.amount]; have hv:= h.families a; exact ⟨hv.sym i,hv.meas i,hv.reads i,hv.permit i⟩
         rw [hf.cleared i ht a]; exact ⟨fun _ _=>rfl,measurable_const,fun _ _ _ _=>rfl,fun U hh=> (hh rfl).elim⟩
      exact ⟨fun i=> (he i).1,fun i k V=> (hw i|>.orientation k V).to_iff, fun i=> (he i).2.1,fun i=> (hw i).measurable,fun i=> (he i).2.2.1,fun i=> (hw i).reads,fun i=> (he i).2.2.2⟩
    intro i a; by_cases ht: i∈Set.range (lens E c)
    · obtain ⟨i,rfl⟩:=ht; unfold Yard.plane; rw [hf.labels,hf.fits,hf.amount]; exact h.invested i a
    rw [hf.cleared _ ht]; exact fun _ _ _ hh=> (hh rfl).elim
end YM.RemainderComparison.Jolt
