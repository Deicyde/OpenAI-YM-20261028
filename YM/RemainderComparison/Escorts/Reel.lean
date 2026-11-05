import YM.RemainderComparison.Escorts.Fues
import YM.RemainderComparison.Ethereal.Pavilion
/-!
 # Readdress COMPULSORY mask slots with new ones BLANK if nonphase
    before the actual REP step. All Budget bookkeeping is on THIS beta/p.
    No identity imported via volume or density projection.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Escorts
open Function Filter Finset Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Push Push.AbsoluteSums PhysicalNext.Repeat
open Merge Mosaic Mosaic.Verse Marker Jolt Flues Ethereal Progress.DirectedRecipe
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c:Side}{ι κ:Type}{α:Type*}
variable (R:Rep G c) (S:Scone ι α G c) (a:α)
local notation "A" => R.activities
local notation "p"=>R.p

def silver (ι:Type)(α:Type*) : Yard ι α G c := ⟨(A).forced,0,fun _=> (A).K⟩
def pitch : Lacuna.Vowel G c ℕ:= ⟨(A).reg,(A).E⟩
local notation "H"=> silver R ι α
local notation "Y"=> pitch R
local notation "C"=> fireplace H S
variable (F:ℕ≃(fireplace (silver R ι α) S).Pellet)
set_option quotPrecheck false
local notation "u"=> (Set.univ:Set ι)
local notation "D" => Flues.flash H S p u F

def plum := (fireplace (silver R ι α) S).encoding.some
variable {δ x z σ B:ℝ} (ρ:ι→Support c)
lemma tender (ht:(A).ForcedFamily p): Yard.Sounds H p ρ:=by
   constructor
   · exact fun _=> ⟨ht.sym,ht.symtest,ht.meas,ht.meas_test,ht.reads,ht.reads_test,ht.permit⟩
   intro i b j hj; exact (Multiset.notMem_zero _ hj).elim
-- Need include α in lemma binder. adapt
lemma pension (h:(A).Valid p δ x): Orbit H u∧ Lacuna.Vowel.Moves Y:=by
    refine ⟨?_,?_⟩
    · refine ⟨fun _ _ _ _=>rfl,fun s t=>?_⟩
      obtain ⟨v⟩:= h.moves s t; refine ⟨v.kp,fun i=>⟨Iff.rfl,?_ ,fun _ V _=>v.valuesK i V⟩⟩
      exact ((Jolt.valids ..).mpr ⟨v.forced_support i,v.forced_inventory i,v.forced_tests i⟩).symm
    refine ⟨fun s t=>?_⟩; obtain ⟨v⟩:= h.moves s t
    have he: ∀ (P Q:RegularAddress c),P.site=Q.site→P.support=Q.support→P=Q:=by rintro ⟨_,_,_⟩ ⟨_,_,_⟩ a b; congr
    exact ⟨v.ep,fun i=> ⟨he _ _ (v.reg_site i) (v.reg_support i),funext fun U=> v.valuesE i U⟩⟩

-- Note T.New K labels transport across phases not preserving score order/card on marked legs. Motion eligibility for ALL Q uses Jolt.
variable (hl:∀ i,Jolt.dawn S Set.univ i→∀ b,S.glow b i=0)
def leather (j:ℕ): C|>.Pellet:= ⟨{Sum.inl j}, by
        refine ⟨⟨j,by simp [lefts]⟩,⟨by simp,?_⟩,?_⟩
        · intro a ha b hb; rw [mem_singleton.mp ha,mem_singleton.mp hb]; exact Relation.ReflTransGen.refl
        simp [lefts,Set.Pairwise]⟩
def strap : ℕ ↪ ℕ:= ⟨F.symm ∘ leather R S, fun _ _ h=> Sum.inl_injective (Finset.singleton_injective (congr_arg Subtype.val (F.symm.injective h)))⟩
local notation "ℓ"=> Escorts.strap R S F

def panorama := Ethereal.manor Y D u a
def photo := {R with activities := panorama R S a F}
local notation "Bʼ" => panorama R S a F
lemma wears (j) : (F (ℓ j)).val={Sum.inl j}:=by rw [show (ℓ j)= F.symm _ from rfl,F.apply_symm_apply]; rfl
lemma skins (j) : ((D).more (ℓ j)).support=((A).forced j).support:=by
    change ((F _).val.biUnion (C).patch)= _; rw [wears]; simp [Pipes.patch,fireplace,silver]
lemma enters {i}(h: ((F i).val).toRight=∅): i∈Set.range ℓ:=by
   obtain ⟨j,hj⟩:= Escorts.winter C (F i) h; exact ⟨j,F.injective (Subtype.ext ((wears ..).trans hj.symm))⟩
include hl
variable (hg:R.activities.ForcedFamily R.p)
include hg
lemma legality : Readdress p (Equiv.refl _).toEmbedding ℓ A Bʼ:=by
   have he (j): ((D).more (ℓ j)).support=((A).forced j).support:= skins R S F _
   have hv (j): ((D).more (ℓ j)).inventory=((A).forced j).inventory:=by
       change (C).plot (F _) = _; unfold plot; rw [wears,show Ovens.lefts {Sum.inl j}={j} from (by ext; simp [Ovens.lefts])]; simp [fireplace,silver]
   have hp (j U) : ((D).more (ℓ j)).extraTest U ↔ ((A).forced j).eligible (p).threshold U:=by
       change condition F p (ℓ j) U ↔ _; unfold condition; rw [wears]; simp [lefts,fireplace,silver]
   have ha j U : ((D).more (ℓ j)).eligible (p).threshold U ↔ ((A).forced j).eligible (p).threshold U:=by
       unfold ForcedAddress.eligible; rw [he,hv,hp]; refine ⟨fun h=>h.2,fun h=>⟨h.1,h⟩⟩
   refine ⟨fun _=>rfl,he,hv,fun i=>?_, fun j=> ?_,fun i h=>(h ⟨i,rfl⟩).elim,fun j hj=> ?_,fun i U=>(ha i U).2⟩
   · rfl
   · have ht : Jolt.phase D u (ℓ j):=by
        apply (Jolt.stars ..).mpr; intro i hi; rw [wears R S F,mem_singleton] at hi; rw [hi]; change load u 0=0; simp [load]
     rw [show (Bʼ).K (ℓ j)= _ from if_pos ht]; ext U; unfold Flues.flash; dsimp only; rw [wears,Finset.prod_singleton]; split
     · rfl
     next H' => exact Eq.symm (Classical.byContradiction (fun hu=> H' ((ha j U).mpr (hg.permit j U hu))))
   by_cases h:Jolt.phase D u j
   · rw [show (Bʼ).K j= _ from if_pos h]; ext U; unfold Flues.flash; dsimp only; split
     · obtain ⟨k,hk⟩:=Finset.nonempty_iff_ne_empty.mpr (show _≠ _ from fun hx:(F j).val.toRight=∅=>hj (enters R S F hx))
       have h1:= mem_toRight.mp hk; change _=0; exact Finset.prod_eq_zero h1 (S.ashes u (congr_fun (hl k ((Jolt.stars ..).mp h _ h1) a) _))
     rfl
   exact if_neg h
omit hg
variable (h:R.activities.Valid R.p δ x)
include h
lemma permits (H': S.Rises p ρ) (ht:Jolt.Whirls S u) : (Bʼ).Valid p δ x:=by
    have hv:= Escorts.legality R S a F hl h.forced; have hh:= Flues.flash_sound H S p ρ u F (Escorts.tender (α:=α) R ρ h.forced) H'; have hp:= Escorts.pension (ι:=ι) (α:=α) R h
    exact ⟨hv.regular h.regular,Ethereal.speaks Y D u a p ρ hh, Ethereal.quiescent Y D u a (Jolt.gathers _ _ _ _ _ hp.1 ht) hp.2,hv.Ebound h.boundE,hv.Kbound h.boundK⟩
omit h
include hg
lemma panorama_eval (U:Config G c) : (photo R S a F).eval U=R.eval U:=by
    unfold Rep.eval Rep.exponent; change Real.exp (R.v* Fintype.card (Site c)- R.path.inChannels R.clip R.p R.beta U - (Bʼ).additive p U)* (Bʼ).gas p U=_; rw [(Escorts.legality R S a F hl hg).same_sum,(Escorts.legality R S a F hl hg).same_gas]

end YM.RemainderComparison.Escorts
