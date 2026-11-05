import YM.Next.UV_STRESS.Birth

/-!
# Signed density projection, product branch of Shell T and B versus counterterm

Difference is at the same placements/copies within cells. `triple`
disallows illegal combinations already in the old system. Project *after*
propagation to birth. Doesn't bound the signed cost by adding the root costs
of the two branches. Exact billed energy factors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Set Function Filter MeasureTheory Measure Analysis Extraction Table Ward Cells Lattice Wilson Overlay Marker RG
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (C : Family G)
variable {N p ℓ k h m d D : ℕ}

section
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- Third name is subtractive. -/
def triple : Census (ι×Fin 3) where
  choices := Finset.univ.filter fun v : Finset (ι×Fin 3) => ∀ i,(i,2) ∈ v → (i,1) ∉ v ∧ (i,0) ∉ v
  blank := by simp
  solo := by
    rintro ⟨i,p⟩; simp; intro j; rw [← j]; decide
  down {x} hx y hy := by
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at *; intro i hh
    exact ⟨fun h => (hx i (hy hh)).1 (hy h),fun h => (hx i (hy hh)).2 (hy h)⟩

variable {ι}
def unionMode (u t : Finset ι) : (triple ι).Mode :=
    ⟨t ×ˢ {2} ∪ (u\t) ×ˢ ({0,1} : Finset (Fin 3)), by
      change _∈Finset.univ.filter _; simp only [Finset.mem_filter, Finset.mem_univ,true_and]
      intro i hi; have h : i∈t := by simpa using hi
      simp [h]⟩



def styles (d D : ℕ) (t : ι × Fin 3) := if t.2=2 then D else if t.2=0 then 4 else d
variable (L : Overlay.Lane C.path (triple ι) N p) (X : Stair C (Stock.census ι) N p)

def group_signal (s : (Stock.census ι).Mode) (k : ℕ) (U : Config G (C.side k p)) :=
    ∑ u∈s.val.powerset, (-1:ℂ)^u.card * L.signal k (unionMode s.val u) U

/-- Uses actual T columns, not T−equation columns. -/
structure Portion (h D d k ℓ : ℕ) : Prop where
  loading : L.load=styles d D
  arrived : L.Works k
  age : 4+d=h+D
  rises : X.Limit C k ℓ (fun _ => D)
  signal (s : (Stock.census ι).Mode) : X.echo C k s = group_signal C L s k




end
end YM.Next.UVStress
