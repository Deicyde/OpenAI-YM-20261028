import YM.MergeProof.Stow
import YM.Push.GRID_APPROXIMATION.Nil



set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type*}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
-- all families compacted by barcode, no spectral cancellation in prices.
structure Borne (o:V→Site n)(P:Support n)(f:Config G n→Poly B)(t:ℝ):Prop where
   home:UsesFinal t P f
   turns:GaugeInvariant f
   me i:Measurable fun U=> (f U).part i
   scope U: GridApprox.Nil.Scoped (A:= {i| o i∈P}) (f U)

structure Burns (o:V→Site n)(P:Support n)(f:Config G n→Poly B)(t:ℝ):Prop extends Borne o P f t where
   permits U:f U≠0→Healthy t P U
   sil U:(f U).part B.quiet=0

def Sure (p:Box n):Prop:=p.2.Nonempty ∧ p.2⊆ p.1
structure Flow (o:V→Site n)(i:Box n)(f:Config G n→Poly B)(t:ℝ):Prop extends Borne o i.1 f t where
   permits U:f U≠0→ i.1∩flags t U=i.2 ∧ Sure i

open GridApprox.Nil
def Loci (w:V→ℝ)(F:Y→Poly B)(a:ℝ):Prop:=∃ v : Sheet B, 0 ≤ v ∧ (∀ U i, ‖(F U).part i‖ ≤ v i) ∧ wordsPrice w v≤a
def Towed (w:V→ℝ)(S:I→Support n)(F:I→Y→Poly B)(b:ℕ)(e u:ℝ):Prop:=∃ a:I→ℝ,Summable a∧Hit S b a e u ∧ ∀ i,Loci w (F i) (a i)
def Mach (B:Census V) (f:V→ℂ)[Fintype V] : Poly B:=∑ i:V,Poly.send (B.fire i) (f i)
def Pattern (s:Support n)(i:Finset (Box n)) :Prop:= (i:Set (Box n)).PairwiseDisjoint (fun p=> p.1) ∧ i.biUnion (fun p=>p.2)=s -- covers. inventory nonempty property by construction.
def grid (f : Box n→Poly B)(s:Support n)(p:Finset (Box n)) :Poly B := if Pattern s p then ∏ i∈p,f i else 0
def field (f : Box n→Poly B)(s:Support n): Poly B:=∑ p:Finset (Box n),grid f s p
def bar (A:Activities G n)(B:Census V)(U:Config G n)(p:Box n):Poly B:= Poly.bead B (profile A (fun i=> Complex.ofReal ∘ A.K i) p U)
-- exponential/H and K profiles separated. No paying ANY singleton here-- value consumed differently each user.
variable [Fintype V]
def rises (P:Poly B):Prop:=∀ i,P.part i≠ 0 → 2 ≤ i.val.card
structure Carton (o:V→Site n) (H:Support n→Config G n→Poly B) (K:Box n→Config G n→Poly B)(t:ℝ):Prop where
   exp (i): Burns o i (H i) t ∧ ∀ U,rises (H i U)
   flag (i): Flow o i (K i) t ∧ ∀ U, rises (K i U)
-- independent singleton carriers: ξ in exponent already masked incl unit, λ profile already compact
variable (R:Rep G n)(Φ:V→Config G n→ℂ)(ωs: V→Box n→Config G n→ℂ)
def restore (H:Support n→Config G n→Poly B) (K:Box n→Config G n→Poly B) (U:Config G n): Poly B:=
  (Real.exp (R.exponent U):ℂ) • (Poly.pass (Mach B (fun i=>Φ i U)+ ∑ i,H i U)* field (fun p=>bar R.activities B U p+Mach B (fun i=> ωs i p U)+K p U) (flags R.p.threshold U))

def Served (X:Config G n→ Poly B) (o:V→Site n)(w:V→ℝ)(e C:ℝ) := ∃ H K, Carton o H K R.p.threshold ∧ Towed w id H R.p.B e C ∧ Towed w (fun p:Box n=>p.1) K R.p.B e C ∧ X=restore R Φ ωs H K
end YM.MergeProof.Accent
