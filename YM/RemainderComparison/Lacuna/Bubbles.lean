import YM.RemainderComparison.Lacuna.Vowel
import YM.RemainderComparison.Jolt.Revel
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Lacuna
open Function Filter Finset Lattice RG Wilson MeasureTheory ProbabilityTheory Ovens
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat Song Slide Trio
open AnalyticBridge VerifiedReset Collection Quotes YM.Extra.Iteration
open Mosaic Mosaic.Verse WickReps Flues Lobby
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c:Side}{ι β I : Type}{α:Type*}[DecidableEq β]
open Vesuvius Jolt
-- Cap petals Glow orientation.Read B rates keep all.Inspects.Final.B.Same
variable (S:Vesuvius G c ι I α) (P:BudgetPoint)(u:Set ι)(a b:α)(roots:ι→Support c)
local notation "Tv"=> Lacuna.shade S u
local notation "P₀" => Jolt.standing c
local notation "F₁" => Seat c× I
-- mark orientation.After logical spins

def bubbles : Vesuvius G c ι (Seat c × I) α where
    site i := i.1.spread (S.site i.2)
    yeah i:= (S.yeah i.2).image _
    log x i:= if i.snd∈ Tv then Song.Rim c • (S.log a i.2 ∘ i.1.view) else if i.fst=P₀ then S.log x i.2 else 0
    opus i:= if i.snd ∈ Tv then 0 else S.opus i.2
local notation "Tt"=> Lacuna.bubbles S u a
lemma gleam x (i:I) : ((x:Seat c),i) ∈ Lacuna.shade Tt u ↔ i∈ Tv:=by
    constructor
    · intro h; by_contra hn
      apply hn; change Verse.load u _=0; change Verse.load u ((Tt).opus _)=0 at h
      rwa [show (Tt).opus (x,i) =S.opus i from if_neg hn] at h
    intro h; change Verse.load u ((Tt).opus _)=0; rw [show (Tt).opus (x,i)=0 from if_pos h]; simp [Verse.load]
lemma presence {i:I}(h:i∈ Tv)(x:Seat c): (Tt).log b (x,i)=Rim c • (S.log a i ∘ x.view):= if_pos h
lemma warms (Sx : Support c)(t:Seat c){x: Config G c→ℝ}(h:Tidy P Sx x): Tidy P (t.spread Sx) (x ∘ t.view):=by
   refine ⟨ProjectorNext.Equivariance.final_pull _ _ _ h.uses,h.borel.comp (show Measurable (t.view : Config G c→ Config G c) from (continuous_pull ..).measurable),?_⟩
   exact Push.Local.invariant_pull h.invariant t.1 t.2 -- check
variable {σ v d:ℝ} (h:S.Works P roots u σ v d)
include h
lemma spools : Vesuvius.Works P roots u Tt σ v d:=by
    have he := gleam S u a
    let f: I ↪ (Seat c × I):= ⟨fun i=>(P₀,i),fun i j h=> congr_arg Prod.snd h⟩
    constructor
    · rintro ⟨x,i⟩ b; by_cases ht:i∈ Tv
      · rw [presence S u a b ht]; exact Trio.tidy_scale P _ (Lacuna.warms P _ _ (h.oasis i a))
      by_cases hv:x=P₀
      · subst x
        rw [show (Tt).log b (P₀,i)= S.log b i from (if_neg ht).trans (if_pos rfl), show (Tt).site (P₀,i)=S.site i from Jolt.stun _]; exact h.oasis i b
      rw [show (Tt).log b (x,i)=0 from (if_neg ht).trans (if_neg hv)]; exact Trio.tidy_const P _
    · rintro ⟨x,i⟩ b; by_cases ht:i∈ Tv
      · rw [show (Tt).opus (x,i)= 0 from if_pos ht]; exact fun j hj=> False.elim (Multiset.notMem_zero _ hj)
      rw [show (Tt).opus (x,i)= S.opus i from if_neg ht]; by_cases hv:x=P₀
      · subst x; rw [show (Tt).log b (P₀,i)= S.log b i from (if_neg ht).trans (if_pos rfl),show (Tt).site (P₀,i)=S.site i from Jolt.stun _]; exact h.quest i b
      rw [show (Tt).log b (x,i)=0 from (if_neg ht).trans (if_neg hv)]; exact fun _ _ _ hh=> (hh rfl).elim
    · rintro ⟨x,i⟩ b U hP; by_cases ht:i∈ Tv
      · rw [Lacuna.presence S u a b ht]; change _*S.log _ _ _= _; rw [h.happy i a _ ((x.healthy ..).1 hP),mul_zero]
      by_cases hv:x=P₀
      · subst x; rw [show (Tt).log b (P₀,i)=S.log b i from (if_neg ht).trans (if_pos rfl)]; exact h.happy i b U ((show (Tt).site (P₀,i)=S.site i from Jolt.stun _) ▸ hP)
      rw [show (Tt).log b (x,i)=0 from (if_neg ht).trans (if_neg hv)]; rfl
    obtain ⟨r,q,hr,hq,hR,hQ,hX⟩:= h.fortune
    let w:= fun i:Seat c × I=> Rim c*r i.2; let w':= Progress.DirectedRecipe.stuff f q
    have hh i : 0 ≤ w i:= mul_nonneg (rim_nn _) (hr _); have hh' i : 0 ≤ w' i:= Progress.DirectedRecipe.Rack.positive _ _ hq i
    refine ⟨w,w',hh,hh',fun i=>?_ ,fun i=>?_,fun i b U=>?_⟩
    · have he:= Cost.nonneg (hR (0:Site c)); nth_rw 1 [show v=(Fintype.card (Seat c):ℝ)*(Rim c*v) by rw [← mul_assoc,balance,one_mul]]
      apply Cost.product (Cost.finite _ (mul_nonneg (rim_nn c) he)); intro p
      let y:=StepData.sendSites p.1 p.2; have hv (x:I): i ∈ (Tt).site (p,x)↔ y.symm i∈S.site x:= (by change i∈ (S.site x).image y ↔ _; rw [show (S.site x).image y=(S.site x).map y.toEmbedding from (Finset.map_eq_image y.toEmbedding _).symm, mem_map_equiv])
      convert Cost.scale (hR (y.symm i)) (Rim c) (rim_nn _) using 2 with j; simp_rw [hv,show coverNumber P.B ((Tt).site (p,j))= _ from Seat.visit_count p (S.site j)]; unfold w; split <;> ring
    · refine Progress.DirectedRecipe.transfer_budget f (fun k=>?_) (fun j hj=>?_) (hQ i)
      · unfold w'; rw [show (Tt).site (f k)= S.site k from Jolt.stun _,Progress.DirectedRecipe.stuffed]
      split; rw [show w' j=0 from Progress.DirectedRecipe.blank _ _ hj,zero_mul]; rfl
    obtain ⟨y,i⟩:=i; by_cases ht:i∈Tv
    · rw [if_pos (show Verse.load u _=0 from (he y i).2 ht)] -- need unfold
      rw [Lacuna.presence S u a b ht]; change ‖Rim c * _‖ ≤ Rim c * r i; rw [norm_mul,Real.norm_of_nonneg (rim_nn _)]
      refine mul_le_mul_of_nonneg_left ?_ (rim_nn _); exact (hX i a _).trans_eq (if_pos ht) -- le.trans_eq
    have hl:(y,i)∉ Lacuna.shade Tt u:= mt (he ..).mp ht
    rw [if_neg (show Verse.load u _≠0 from hl)]; by_cases hv:y=P₀
    · subst y; rw [show (Tt).log b (P₀,i)=S.log b i from (if_neg ht).trans (if_pos rfl),show w' (P₀,i)= q i from Progress.DirectedRecipe.stuffed f q i]; exact (hX i b U).trans_eq (if_neg ht)
    rw [show (Tt).log b (y,i)=0 from (if_neg ht).trans (if_neg hv)]; simpa using hh' (y,i)
end YM.RemainderComparison.Lacuna
