import YM.Next.RANK.Stall

set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Finset Function Filter MeasureTheory Lattice Wilson RG Marker Source 
open Next.Rank Edition Baler Value Glyph Thirst Alarm   
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]
variable (o: V → Site n)
variable {u v t e:ℝ} {ι κ:Type} [Fintype ι] [Fintype κ]
variable {Q:Rep G n}
local notation "A"=> Q.activities
variable {d:V → ℕ}{F:(i:V)→ Labels.Frame G (d i)} (T:(i:V)→SectionData (F i)) (D:(i:V)→Coefficient (F i) n)
   {η:Hol G} (h:∀ i,(D i).Format 0 η Q)(s:V→Signed)(x:V→Prop)
   (B:Neat n → Burst G n Q.p.threshold)(β:V→ℂ)(hb:∀ i,star (β i)=β i)

def bitsX (j:V) := chip (s j) (h j) (x j) (β j) (ζ:=o) j
def elderX (i : Elders n V) := Sum.elim (enroll o ∘ B) (fun p=> bitsX o D h s x β p.1 p.2) i
variable (C0:κ→ Lifted G o Q.p.threshold)(L:ι→ SourceAt G o)
def gamutX (U:Config G n)(i:Neat n):veil V:=∑ j:Elders n V⊕κ,
    let p:= Sum.elim (elderX o D h s x B β) C0 j
    if attached p=i then p.amount U else 0
lemma all_gasX (U : Config G n) : ∑ i : Finset (Neat n), peeled id (gamutX o D h s x B β C0 U) (flags Q.p.threshold U) i =
    ∑ i:Finset _,Lifted.pack (Sum.elim (elderX o D h s x B β) C0) i U:= by
  simp_rw [gather_plate]; symm
  let F:=Sum.elim (elderX o D h s x B β) C0; let V t:= (F t).amount U; let g t:=attached (F t)
  refine Eq.trans ?_ (Eq.trans (Baler.some g V (flags Q.p.threshold U) univ) ?_)
  · rw [Finset.powerset_univ]
  apply congr_arg (fun f=>∑ i : Finset (Neat n),peeled id f (flags Q.p.threshold U) i); ext1 i
  unfold gamutX; rw [sum_filter]

def credsX (U : Config G n) := (Real.exp (Q.exponent U):ℂ) • (
    Poly.pass ((∑ i : V,Poly.send (slot i) (dot (x i) ((β i)*(D i|>.exponentialEntry 0 (T i) Q (pull (s i) (o i) U)))))+
      (∑ i,(L i).amount Q.p.threshold U)) * ∑ j:Finset _, Lifted.pack (Sum.elim (elderX o D h s x B β) C0) j U)

end YM.Next.Rank.Edition