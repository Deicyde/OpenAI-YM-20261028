import YM.OPE.Schemes.Travel

/-! # All-character tested truncations

Both normative versions are stated because an application might want the cost
of a vacuum ground element, or actual expectations in a particular law. All
terms (product **and** subtractions) use complete expectations, not connected.
Fields of every type & filtration stage can be included on either side,
including nil exteriors and identity tokens. `viewing` totalizes off Conf,
actual estimates only use the indicated separated configurations. `worded`
compresses our naming presentation but uses precisely the underlying (and all
character phase) laws. On Conf both include their unit terms. This is the
single overall discrepancy.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Set Filter Lattice RG Next.Extract Bid OS Ground Spec
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G} {F:Extraction.Order} {S:Table C.book} (U:Final C F S)
variable {I J K:Type}[Fintype I][Fintype J]
variable (P:Prescription U.sector.derivatives) (n:ℕ)
    (x:I→ E4)(p:I→ C.book.Token)(o:E4)(y:J→ E4)(q:J→ C.book.Token)
    (a:Mode U.sector.derivatives)(r:Viewers U)

def groundError : U.α.unselected.algebra :=
    viewing U (beside x y) (beside p q) - ∑ i∈ bands U.sector.derivatives n, (P.ope i x p o) • viewing U (beside (sole o) y) (beside (sole (P.letter i)) q)
-- groundError shape `(v:X follow U)`
lemma glance_terms (hx:Injective (beside x y))(hy:Injective (beside (sole o) y)) : glance U r (groundError U P n x p o y q)= observe (spectator U r) (beside x y) (beside p q) - P.truncated (spectator U r) n x p o y q := by
    unfold groundError Prescription.truncated Prescription.termRead; rw [map_sub, map_sum]; simp only [map_smul,glance_sees U _ _ _ hx,glance_sees U _ _ _ hy]; rfl

/-- Norm bound, and uniform over all phases **and** the unselected law. On
Conf, `usable` results on expectations with exactly those tokens can use this.
-/
structure Tested (u:ℝ): Prop where
    compressed : ‖groundError U P n x p o y q‖ ≤ u
    phaseBound (r:Viewers U): ‖observe (spectator U r) (beside x y) (beside p q)-P.truncated (spectator U r) n x p o y q‖ ≤ u

variable {T:K→ℝ} {φ:Filter K} {X:K→I→ E4}{O:K→E4}{Y:K→J→E4}{s u v κ:ℝ}
lemma tested {u:ℝ}(hb:‖groundError U P n x p o y q‖ ≤ u)(hx:Injective (beside x y))(hy:Injective (beside (sole o) y)): Tested U P n x p o y q u :=
    ⟨hb,fun r=> (congr_arg norm (glance_terms U P n x p o y q r hx hy)).symm ▸ ((glance_bound U _ _).trans hb)⟩ -- rewrite norm orientation?

/-- Uniform estimates for `Viewers`: once they can vary in the exponential-rate
statement, one eventually can require a bound at all of them. -/
lemma universalize {V : Type*}[Nonempty V]{p: K→ V→ Prop}(h:∀ f:K→V,∀ᶠ i in φ, p i (f i)): ∀ᶠ i in φ, ∀ v:V, p i v:= by
    let f := fun i=> if hp:∃ v, ¬ p i v then hp.choose else Classical.arbitrary _
    filter_upwards [h f] with i hi v; change p i (if hp:∃ v, ¬ p i v then hp.choose else Classical.arbitrary _) at hi; split at hi; next hv => exact (hv.choose_spec hi).elim
    next he=> exact Classical.byContradiction fun hp=> he ⟨v,hp⟩
lemma ground_cost (hx:∀ᶠ i in φ,Injective (beside (X i) (Y i)))(hy:∀ᶠ i in φ,Injective (beside (sole (O i)) (Y i)))
    (h: ∀ f:K→ Viewers U, RateLE φ T (fun i=> observe (spectator U (f i)) (beside (X i) (Y i)) (beside p q) - P.truncated (spectator U (f i)) n (X i) p (O i) (Y i) q) κ): RateLE φ T (fun i:K=> groundError U P n (X i) p (O i) (Y i) q) κ:=by
    intro d hd; filter_upwards [universalize (p:=fun i f=> ‖observe (spectator U f) (beside (X i) (Y i)) (beside p q) - P.truncated (spectator U f) n (X i) p (O i) (Y i) q‖ ≤ Real.exp (d*T i)) (fun f=>h f d hd),hx,hy] with i hf hx hy
    refine (glance_contract U (Real.exp_nonneg _)).2 (fun r=>?_); rw [glance_terms U P n (X i) p (O i) (Y i) q r hx hy]; exact hf r

/-- Proof hypotheses bundle. For all upper bounds; *not* data of a different table.*
    Producible on the same actual Final. -/
structure Services (C:Family G)(F:Extraction.Order)(S:Table C.book) : Prop where
   schedule : Org.Grill C F
   simpleGate : G.Simple
   purchase : ∃ W r D, Package C W r D
   along : ∃ M V E H, Base C F M V E S H

variable (hT:Tendsto T φ atTop)[φ.NeBot] (h : Services C F S) [DecidableEq I][DecidableEq J]
variable (he:P.Coherent)(hx:enveloped φ T s X O)(hk:Kept φ T s X)(hs:0<s)
include h hT he hx hk hs
lemma available_cost (i:Mode U.sector.derivatives) : RateLE φ T (fun i'=> P.ope i (X i') p (O i')) (((sigma p:ℝ)-(i.fst:ℝ))*s):=by
    obtain ⟨c,hG,⟨b,u,a,l⟩,H⟩:= h; obtain ⟨M,Y,E,W,H⟩:= H; exact group_coeff U p H hT hG l c he hx hk hs i -- arg order inspect
-- lemma room_cost needs Bundle etc
lemma arrangement_cost (hq:Kept φ T v Y) (hf:Intervals φ T u (fun i=> sole (O i)) Y)(hu:0≤u)(hv:u≤v)(hp:u<s): RateLE φ T (fun i:K=> groundError U P n (X i) p (O i) (Y i) q) ((sigma p:ℝ)*s-(n+1:ℝ)*(s-u)+(sigma q:ℝ)*v):= by
    obtain ⟨c,hG,⟨b,u',a,l⟩,H⟩:= h; obtain ⟨M,V,E,W,H⟩:= H;
    apply ground_cost U P n p q ((hk.mono (le_max_left s v)|>.chorus (hq.mono (le_max_right ..)) ((Rec_spacing hT hf hx hp).mono (hv.trans (le_max_right ..))))|>.inject) ((Kept.sole φ T O v|>.chorus hq (hf.mono hv))|>.inject);
    intro r; exact group_remainder U p q H hT hG l c he hx hk hs r hf hq hv hp hu n
end YM.OPE
