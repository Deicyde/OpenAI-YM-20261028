import YM.Next.RANK.Flux.Carrier
import YM.Next.RANK.Flux.Radius

/-! Merging with either holes attachments or final occupancy pressure. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory
open scoped BigOperators Classical

variable {V ι κ : Type*} [DecidableEq V] [Fintype V] {G : Gauge} {n : Side} {ζ : V→ Site n} {t : ℝ}
variable (S : ι→ Plug G ζ t) (P : κ → Lining G ζ t)

def speck (i : ι ⊕ κ) : CoverReads G ζ t:= Sum.elim (CoverReads.ofPlug ∘ S) (raised ∘ P) i
def dish (i) := (speck S P i).extent
lemma dishfest (i) : dish S P (.inl i)=(S i).extent:=p_coverFest _
def fest (i : ι) (j : κ) := meets (dish S P) (.inr j) (S i).extent ∧ (solute (P j) → (S i).landed)
def earns (j : κ) (s : Finset ι):= ∃ i∈s, fest S P i j

def glasses (s : Finset (ι ⊕ κ)):= (s.toLeft:Set ι).PairwiseDisjoint (fun i=>(S i).extent) ∧ ∀ j∈s.toRight,earns S P j s.toLeft
abbrev Party := { s : Finset (ι ⊕ κ) // Spark (dish S P) s ∧ glasses S P s }
def lamps (p : Party S P):= p.val.biUnion (dish S P)
def vital (p : Party S P):= p.val.toLeft.biUnion (fun i=>(S i).inventory)
def shining (p : Party S P): modes V:= scene (p.val.biUnion fun i=> (speck S P i).fires.val)
def toast (p : Party S P) (U : Config G n) : veil V:= ∏ i∈p.val,(speck S P i).covets U
variable (p : Party S P)
lemma leaning : p.val.toLeft.Nonempty:= by
  obtain ⟨i|j,hp⟩:=p.property.1.1; exact ⟨i,mem_toLeft.mpr hp⟩
  obtain ⟨i,hp,H⟩:=p.property.2.2 j (mem_toRight.mpr hp); exact ⟨i,hp⟩
lemma spans {i} (h : i∈p.val): dish S P i⊆lamps S P p:= fun _ hy=> mem_biUnion.mpr ⟨_,h,hy⟩
lemma spines : vital S P p⊆lamps S P p:= by
  intro x hx; obtain ⟨i,hi,hv⟩:= mem_biUnion.mp hx
  exact spans S P p (mem_toLeft.mp hi) ((dishfest S P i).symm ▸ ((S i).mem_extent hv))
lemma beams i (h : i∈ (shining S P p).val):ζ i∈ lamps S P p:= by obtain ⟨j,hj,h⟩:=mem_biUnion.mp h; exact spans S P p hj ((speck S P j).remembers _ h)
lemma toasting (U):Poly.send (shining S P p) ((toast S P p U).part (shining S P p))=toast S P p U:= by
  unfold toast CoverReads.covets; rw [plasma]; split
  · rename_i h; change Poly.send _ ((Poly.send (shining S P p) _).part _)= _; rw [Poly.part_send,if_pos rfl];rfl
  simp only [Poly.part_nil, Poly.send_zero]
lemma go_raid U u (H : Agrees (lamps S P p) U u) (ht : lamps S P p ∩ flags t U=lamps S P p ∩ flags t u):toast S P p U=toast S P p u:= by
  apply prod_congr rfl; intro j hj; unfold CoverReads.covets;apply congr_arg; exact Work.H03.reads_larger (spans S P p hj) (speck S P j).only _ _ H ht
lemma go_inv (U) (i) : toast S P p (gauge i U)=toast S P p U:=by apply prod_congr rfl; intro j _; exact congr_arg (Poly.send _) ((speck S P j).inv i U)
lemma guards : MeasurableSet {U | lamps S P p ∩ flags t (U : Config G n)=vital S P p} := by
  rw [show {U : Config G n| lamps S P p ∩ flags t U=vital S P p}=
    ⋃ m:{x:Support n // lamps S P p ∩x=vital S P p}, {U| flags t U=m.val} by
    ext; simp]
  exact MeasurableSet.iUnion fun _ => flags_measurable_eq ..
lemma measure (v : modes V) : Measurable fun U=> (toast S P p U).part v:= by
  simp_rw [toast,CoverReads.covets,plasma]; split
  · simp_rw [Poly.part_send]; split;exact Finset.measurable_fun_prod _ (fun i _=> (speck S P i).meas); exact measurable_const
  exact measurable_const

def tint (U):= lamps S P p ∩ flags t (U : Config G n)=vital S P p
def Capsules (h : (vital S P p).Nonempty) : Lifted G ζ t where
  extent := lamps S P p
  inventory:= vital S P p
  needed := h
  records:= spines S P p
  fires:= shining S P p
  remembers:= beams S P p
  value U:= if tint S P p U then (toast S P p U).part (shining S P p) else 0
  meas:= Measurable.ite (guards S P p) (measure S P p _) measurable_const
  flag U he:= by split at he;exact (by assumption : tint _ _ _ U);contradiction
  only U u h he:= by
    dsimp only; rw [go_raid S P p U u h he]; by_cases H:tint S P p u
    · rw [if_pos H,if_pos (show tint S P p U from he.trans H)]
    rw [if_neg H,if_neg (show ¬ tint S P p U from fun h=>H (he.symm.trans h))]
  inv k U:= by simp_rw [tint,gauge_flags,go_inv]; congr
lemma patriot (h) (U): (Capsules S P p h).amount U= if tint S P p U then toast S P p U else 0:= by
  unfold Lifted.amount Capsules; dsimp only; split
  · rename_i hp; exact toasting ..
  rename_i hh; exact Poly.send_zero ..

variable (h : ¬ (vital S P p).Nonempty)
include h p
lemma cool {i} (hi : i∈p.val.toLeft): ¬ (S i).landed:= by
  rintro ⟨x,hx⟩; exact h ⟨x,mem_biUnion.mpr ⟨_,hi,hx⟩⟩
theorem courted : (shining S P p).val.Nonempty:= by
  obtain ⟨i,hi⟩:= leaning S P p
  obtain ⟨s,hz⟩:=Plug.innocent (cool S P p h hi); obtain ⟨j,hj⟩:=s.chosen
  refine ⟨j,mem_biUnion.mpr ⟨Sum.inl i,mem_toLeft.mp hi,?_⟩⟩; change _∈ (CoverReads.ofPlug _).fires.val;rw [hz];exact hj
lemma bric (i) (hp : i∈p.val): ∃ q : Inner G ζ, speck S P i = q.glow t:= by
  cases i with
  | inl i=>
    obtain ⟨s,hz⟩:=Plug.innocent (cool S P p h (mem_toLeft.mpr hp)); exact ⟨toInner s, by change CoverReads.ofPlug _=_; rw [hz];rfl⟩
  | inr i=>
    obtain ⟨j,hj,_,hb⟩:= p.property.2.2 i (mem_toRight.mpr hp)
    have hx:¬ solute (P i):=fun H=>cool S P p h hj (hb H)
    match Hl:P i with
    | .inl s=> exact ⟨s,by change raised _=_; rw [Hl];rfl⟩
    | .inr s=> exact False.elim (hx (show solute (P i) by rw [Hl];exact True.intro))

def noted (U : Config G n) (i : ι ⊕ κ) := if hp:i∈p.val then ((bric S P p h i hp).choose).value U else 0
omit h in
def single := (p.val:Set _).PairwiseDisjoint (fun i=> (speck S P i).fires.val)
def soloWell : SourceAt G ζ where
  extent:= lamps S P p
  fires:= shining S P p
  chosen:= courted S P p h
  remembers:=beams S P p
  value U:= if single S P p then ∏ i∈p.val, noted S P p h U i else 0
  meas:= by
    by_cases h:single S P p; swap
    · simp [h]
    simp_rw [if_pos h]
    exact Finset.measurable_fun_prod _ (fun i H=> by simp_rw [noted,dif_pos H]; exact (bric S P p (by assumption) i H).choose.meas)
  inv i U:= by split_ifs; apply prod_congr rfl; intro j hj; simp only [noted,dif_pos hj]; exact (bric S P p h j hj).choose.inv ..; rfl
  loc U u ht:= by
    split
    · rename_i H;apply prod_congr rfl; intro i hi
      have he:= bric S P p h i hi; simp only [noted,dif_pos hi]; apply he.choose.loc
      apply agrees_mono ht; intro x hx; refine spans S P p hi ?_; unfold dish; rw [he.choose_spec]; exact hx
    rfl
lemma elegant U: (soloWell S P p h).amount t U=toast S P p U:= by
  let z:=p.val
  unfold SourceAt.amount soloWell; dsimp only
  unfold toast CoverReads.covets; rw [plasma]
  have hc : ∀ i∈p.val,∀ (_hp : Healthy t (dish S P i) U),noted S P p h U i=(speck S P i).value U:= by
    intro i hi hx; have e:= bric S P p h i hi
    rw [noted, dif_pos hi]; let A:=e.choose; change A.value _=_; rw [e.choose_spec]; unfold dish at hx; rw [e.choose_spec] at hx; exact (masked_eq _ _ _ _ hx).symm
  by_cases hv:Healthy t (lamps S P p) U
  · rw [masked_eq _ _ _ _ hv]; split_ifs with H hx hx
    · apply congr_arg; exact prod_congr rfl fun i hi=> hc i hi (Disjoint.mono_left (spans S P p hi) hv)
    · contradiction
    · contradiction
    exact Poly.send_zero _
  rw [masked_ne _ _ _ _ hv,Poly.send_zero]; split;swap
  · rfl
  obtain ⟨x,hx,hH⟩:= not_disjoint_iff.mp hv; obtain ⟨i,hi,hQ⟩:= mem_biUnion.mp hx
  have he:= bric S P p h i hi
  have hp':(speck S P i).value U=0:= by
    rw [he.choose_spec];apply masked_ne; unfold dish at hQ;rw [he.choose_spec] at hQ; exact not_disjoint_iff.mpr ⟨x,hQ,hH⟩
  rw [prod_eq_zero hi hp',Poly.send_zero]

omit h

def panel : Plug G ζ t := if h:(vital S P p).Nonempty then .raid (Capsules S P p h) else .regular (soloWell S P p h)
lemma pan_extent : (panel S P p).extent=lamps S P p:= by unfold panel;split <;>rfl
lemma pan_vital : (panel S P p).inventory=vital S P p:= by unfold panel;split; rfl; exact (Finset.not_nonempty_iff_eq_empty.mp (by assumption)).symm
lemma pan_mark : (panel S P p).fires=shining S P p:= by unfold panel;split <;>rfl
lemma pan_price (U : Config G n) : (panel S P p).tolls U = if (vital S P p).Nonempty ∧ ¬ tint S P p U then 0 else toast S P p U:= by
  unfold panel; split_ifs with h he he
  · exact (patriot S P p h U).trans (if_neg he.2)
  · exact (patriot S P p h U).trans (if_pos (Classical.byContradiction fun hn=>he ⟨h,hn⟩))
  · exact False.elim (h he.1)
  exact elegant S P p h U
end YM.Next.Rank.Flux
