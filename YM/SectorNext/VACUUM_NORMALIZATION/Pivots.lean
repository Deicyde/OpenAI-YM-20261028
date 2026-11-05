import YM.SectorNext.VACUUM_NORMALIZATION.Mast

/-!
# Pay all but four after spanning tree: face geometry

`earlier i j`: strictly smaller priority i survives longer. j+ axis
preceding coordinate wraps with the torus conventions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum.Masts
open Lattice Tree RG Wilson Filter Finset Function
open scoped Matrix.Norms.Frobenius BigOperators Topology Classical
variable {n : Side} {G : Gauge}

-- axis helpers


def vertical (i : Tor n) := top (i:Link n)
private lemma north (i : Tor n) (hi : vertical i) : ((i:Link n).1) (i:Link n).2= -1 := by
  by_contra he; exact i.property.1 ⟨hi,he⟩
private lemma down (i : Tor n) (hi : ¬vertical i) : (i:Link n).2 < highest (i:Link n).1 := by
  unfold vertical at hi; rw [top_le] at hi; exact lt_of_not_ge hi

def base (i : Tor n) : Site n := (i:Link n).1+step (i:Link n).2
private lemma base_ne (i : Tor n) (_ : vertical i) : base i ≠ 0 := by
  intro he; apply i.property.2; unfold base at he; exact Prod.ext (eq_neg_of_add_eq_zero_left he) rfl
private lemma bottom_entry (i : Tor n) (hi : vertical i) : highest (base i) < (i:Link n).2 := by
  apply lt_of_not_ge
  intro hj
  apply highest_on (base i) (base_ne i hi)
  nth_rewrite 1 [base]; rcases lt_or_eq_of_le hj with hv|hv
  · simp [hv.ne',hi _ hv]
  rw [←hv,Pi.add_apply,step_apply,if_pos rfl,north i hi,neg_add_cancel]

/-- Face in stored positive orientation; both cases have i<j with last
axis vertical. -/
def lens (i : Tor n) : Face (Per n) :=
    if h : vertical i then
      ((i:Link n).1-step (highest (base i)), ⟨(highest (base i),(i:Link n).2),bottom_entry i h⟩)
    else
      ((i:Link n).1-step (highest (i:Link n).1),⟨((i:Link n).2,highest (i:Link n).1),down i h⟩)



-- ranking bigger eliminated first.
def stage (i : Tor n) := if vertical i then (i:Link n).2 else highest (i:Link n).1



















-- Cannot be using the same Face twice. Can prove by geometry or test on
-- a genuinely nontrivial *auxiliary* group (only proving combinatorics!). 


end YM.SectorNext.Vacuum.Masts
