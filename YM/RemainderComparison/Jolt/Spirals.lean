import YM.RemainderComparison.Jolt.Padding
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
-- Mint A.Veras.ld
variable (E:I ↪ ℕ)
local notation "F₀"=> Diadem E c
local notation "P₀"=> standing c
local notation "Ω"=> scope E c
local notation "Lp"=> Jolt.lens E c
local notation "W₀" => clue H E
variable (s:Signed)(b:Site c) (e : Equiv.Perm I)

structure Sleeps : Prop where
    spears i: phase H u (E i)
    quiet i : phase H u i→∀ (a b:α),H.glow a i=H.glow b i
    jets i : i∉Set.range E→ phase H u i→ ∀ a,H.glow a i=0
    spins (s:Signed)(b:Site c) : ∃ e: Equiv.Perm I,∀ i, H.more (E (e i))=Jolt.spring (H.more (E i)) (s,b)∧ ∀ a U, H.glow a (E (e i)) U = H.glow a (E i) (pull s b U)
-- edit s syntax

variable (h:Sleeps H u E)
-- link
lemma asks (x:I) : Jolt.rises E (c:=c) (E x)= Sum.inl x:=by
    have ht: E x∈ Set.range E:= ⟨x,rfl⟩
    unfold rises; rw [dif_pos ht,E.injective (Classical.choose_spec ht)]
lemma whenIn (x: I) : (Ω).symm (Sum.inl x)=Lp (E x):=by apply (Ω).injective; rw [Equiv.apply_symm_apply,leagues,asks]
lemma whenOut (x:Extra E) : (Ω).symm (Sum.inr (P₀,x))=Lp x.val:=by apply (Ω).injective; rw [Equiv.apply_symm_apply,leagues]; unfold Jolt.rises; rw [dif_neg x.prop]
include h
lemma ghost (t:Seat c)(i: Jolt.Extra E)(ht:phase H u i.val) (a:α): (W₀).glow a ((Ω).symm (Sum.inr (t,i)))=0:=by
    have he:= imprint H E; by_cases hp:t=P₀
    · rw [hp,whenOut,he.amount]; exact h.jets _ i.prop ht a
    refine he.cleared _ ?_ a; rintro ⟨j,hj⟩; have hv : Jolt.rises E j=Sum.inr (t,i):=(leagues E j).symm.trans ((congr_arg (Ω) hj).trans ((Ω).apply_symm_apply _)); unfold rises at hv; split at hv
    next h=> exact Sum.inl_ne_inr hv
    next h=> exact hp (congr_arg (Prod.fst) (Sum.inr.inj hv)|>.symm)
lemma spirals : Orbit W₀ u:=by
   have he := Jolt.imprint H E; constructor
   · intro i ht a b
     by_cases hh : i∈ Set.range (Lp)
     · obtain ⟨i,rfl⟩:=hh; rw [he.amount,he.amount]; unfold phase at ht; rw [he.labels] at ht; exact h.quiet i ht a b
     rw [he.cleared i hh a,he.cleared i hh b]
   intro s b; obtain ⟨e,hx⟩:= h.spins s b
   let W:=Equiv.sumCongr e (Song.whirl (ι:= Extra E) s b)
   let x:= ((Ω).trans W).trans (Ω).symm; refine ⟨x,fun i=>?_⟩
   have hi (i:F₀): x ((Ω).symm i)=(Ω).symm (W i):=congr_arg (Ω|>.symm) (congr_arg W ((Ω).apply_symm_apply _))
   obtain ⟨i,rfl⟩:= (Ω).symm.surjective i; rw [hi]
   rcases i with i|⟨t,i⟩
   · rw [show W (Sum.inl i)=Sum.inl (e i) from rfl,whenIn,whenIn, he.fits,he.fits]
     have hv j : phase W₀ u (Lp (E j)):=by unfold phase; rw [he.labels]; exact h.spears j
     refine ⟨iff_of_true (hv _) (hv _),(hx i).1,fun _ V a=>?_⟩; rw [he.amount,he.amount]; exact (hx i).2 a V
   have hv:= h.jets _ i.prop; let y k:=(Ω).symm (Sum.inr (k,i))
   have ht' k : phase W₀ u (y k) ↔ phase H u i.val:=by unfold Jolt.phase clue y; dsimp only [Function.comp_apply]; rw [Equiv.apply_symm_apply]; rfl
   have hp k: (W₀).more (y k)=spring (H.more i.val) k:=by unfold Jolt.clue y; dsimp only [Function.comp_apply]; rw [Equiv.apply_symm_apply]; rfl
   let t':= Seat.move s b t; change (phase W₀ u (y t')↔ phase W₀ u (y t)) ∧ (W₀).more (y t')= _ ∧ (phase W₀ u (y t)→ ∀ (V:Config G c) a,(W₀).glow a (y t') V=(W₀).glow a (y t) (pull s b V))
   refine ⟨(ht' t').trans (ht' t).symm, by rw [hp, show (W₀).more ((Ω).symm (Sum.inr (t,i)))=_ from hp t]; exact Jolt.movement ..,fun hh V a=>?_⟩ -- shadow
   unfold y; rw [Jolt.ghost H u E h t' i ((ht' _).1 hh) a,Jolt.ghost H u E h t i ((ht' _).1 hh) a]; rfl
end YM.RemainderComparison.Jolt
