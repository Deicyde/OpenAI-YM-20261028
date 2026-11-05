import YM.MergeProof.North.Billow
import YM.OPE.Grouping.Family
import YM.OPE.Grouping.Farr

/-!
# Copy coherence after arbitrary simultaneous grouping

Generalizes the one-reap Harmony proof in YM/MergeProof/North/Billow.lean;
output perms & budget in the remaining live polynomials. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Fibers
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V][Fintype V] {n:Side}{G:Gauge}{B:Census V}
variable {X₀ : Type*} [Fintype X₀][DecidableEq X₀] {Δ : Fibers X₀ V} {a₀:Equiv.Perm X₀}
open Extra.Histories Push Push.Local Motion
namespace CopyFamily
variable {Z:Salt V X₀ Δ G n} {t:ℝ}{b:Equiv.Perm V}{m:Motion}{x:Site n}{v u:Set V}
variable (D:Deck V X₀ Δ I J G n)(E:Equiv.Perm I)(F:Equiv.Perm J)
local notation "P"=> Equiv.sumCongr E F
structure Glow (u v:Set V)(m:Motion)(x:Site n)(b:Equiv.Perm V) (a₀ : Equiv.Perm X₀) :Prop where
    permutes : Permutes Δ a₀ b
    lives i: Focus Δ u (D.mode_ i) ↔ Focus Δ v (D.mode_ (Equiv.sumCongr E F i))
    paint i: Focus Δ u (D.mode_ i) →
        D.mode_ (Equiv.sumCongr E F i) = pars a₀ (D.mode_ i) ∧ D.cover (Equiv.sumCongr E F i)=sky m x (D.cover i) ∧ D.toll (Equiv.sumCongr E F i)=stepUp m x (D.toll i)
    hot i : Focus Δ u (D.mode_ (.inl i))→ (D.ash i↔ D.ash (E i))
    flood i: Focus Δ u (D.mode_ (.inr i))→ D.spill (F i)=puff m x (D.spill i)
local notation "K"=> Z.vessel t
lemma orbital (h:CopyFamily Z t m x v u a₀ b) : ∃ E:Equiv.Perm Z.Seed,∃ F:Equiv.Perm Z.Brook,Glow (K) E F v u m x b a₀:=by
    obtain ⟨E,hE,he⟩:= h.perch; obtain ⟨F,hF,hf⟩:= h.blade
    let e:=Equiv.prodCongr E (Equiv.refl Bool); let f:=Equiv.sumCongr e F
    refine ⟨e,F,h.groups, fun i=>?_,fun i hi=> ?_,fun i _ => Iff.rfl,fun i hi=> (hf i hi).1⟩
    · cases i; next i=> exact hE i.1
      next i=> exact hF _
    rcases i with i|i
    · obtain ⟨hm,hd,hv⟩:= he i.1 hi; have hQ : (K).cover (f (Sum.inl i)) = sky m x ((K).cover (.inl i)):=by change Z.kiln (Z.leaf (E i.1)) (Z.marker (E i.1))= _; rw [hm,hd]; exact h.kilo (Z.marker i.1) hi (Z.leaf i.1)
      refine ⟨hm,hQ,funext fun U=>?_⟩
      change (if Healthy _ ((K).cover (f (.inl i))) U ↔ i.2=true then Z.syrup (E i.1) U else 0)=scalar m (if Healthy _ ((K).cover (.inl i)) _ ↔ _ then _ else 0)
      rw [hQ,shading,healthy_pull,hv]; split; next=> rfl
      next=> exact (scalar_z _).symm
    obtain ⟨hj,hk⟩:=hf i hi; refine ⟨hk,?_,funext fun U=>?_⟩
    · change Z.kiln (F i).val.1.1 (F i).val.2=_; rw [hk,hj]; exact h.kilo i.val.2 hi _
    change (Z.river (F i).val.1 U).part (F i).val.2=_; rw [hj,hk]; exact h.jets _ hi _ _
end CopyFamily
end YM.MergeProof.Ribbons.Fibers
