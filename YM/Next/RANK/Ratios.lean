import YM.Next.RANK.Canal
import YM.Next.RANK.Festoon
import YM.Next.RANK.Fleet

/-!
# Rates through actual arcs; growth MUST be paid before L
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function MeasureTheory Filter Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation EntryWord
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V Ω : Type*}
variable {C : Family G} {i k l j m p q d D a N : ℕ} {R : Lead G C.S p}
variable {hN : k≤N} {b : ℝ} {x : Points m} {hk : i≤k} {hi : middle C.path.levels b k ≤ i}
variable {c : Course C N p k}

-- clock requests
structure Purse where
  era : Era
  taylor : ℕ -- charge cap d+ poly order through D
  goal : ℕ
  horizon : ℕ
  band : ℝ
  credit : ℝ
  f : ℝ -- shrink log radius
  foil : ℝ -- positive j budget
  L : ℝ -- Kernel projections pre bound
  positive : 0 ≤ foil
  loan : 1≤L
  motion : 1≤credit
  fits : f + credit ≤ -8
  spend : era.coast.e ≥ 0
  tolerance : 6 ≤ goal
  warp : 2*era.coast.V + 2 ≤ (goal:ℝ)-1
  hour : 1/16-era.coast.U=f
  common : era.coast.V=era.coast.U

variable (D' : Purse)
namespace Purse
def principal (b : Purse) (s : ℝ) := Perch.bill b.credit s
def ledger (b : Purse) (s : ℝ) := principal b s* Perch.bill 1 s
def double (b : Purse) (s : ℝ) := Perch.bill (2*b.credit+3) s
def cash (b : Purse) (s : ℝ) := Perch.bill b.f s
def demand (b : Purse) (s : ℝ) := Perch.bill (-(b.goal:ℝ)) s
def sends (b : Purse) (s : ℝ) := Perch.bill (-b.foil) s
lemma stock_pos (b : Purse) (s) : 0 < b.ledger s:= mul_pos (Real.exp_pos _) (Real.exp_pos _)
lemma ledger_lo (b : Purse) (s) : b.ledger s ≤ b.double s:= by unfold ledger principal double; rw [overlap]; exact Glimmer.billed s (by linarith [b.motion])
lemma cash_le (b : Purse) (s): cash b s ≤ 1:= by unfold cash; exact (Glimmer.billed _ (show b.f ≤ 0 by linarith [b.motion,b.fits])).trans (by simp [bill])

def race (b : Purse) := b.era.α+2
lemma running (b : Purse) : 1≤ b.race:= by unfold race; linarith only [b.era.pay]
-- Pre-L cost for R; expose k,m factors p all bought.
def epoch (b : Purse) (s : ℝ) (j : ℕ) := race b ^ j * b.demand s
lemma profit (b : Purse) (s : ℝ) (j : ℕ): b.demand s ≤ epoch b s j:= le_mul_of_one_le_left (Real.exp_pos _).le (one_le_pow₀ b.running)
end Purse

-- predetermined height price: acquired from scale after large enough L. radius spends per k uniform.

def torque (s : ℝ) := 3*hot s
def knox (s : ℝ) := bill 1 s

structure Racer (b : Purse) (s : ℝ) (h : ℕ) : Prop where
  log : b.race^h≤Perch.bill 1 s
  one : hike b.L b.taylor h ≤ Perch.bill 1 s
  two : hike b.L (2*b.taylor) h ≤ Perch.bill 1 s
  cone : b.principal s^2*Perch.bill 1 s+b.ledger s^2 ≤ b.double s
  family : (h:ℝ)≤ Perch.bill 1 s

-- smoothing estimate post expense for T:q moves. g≤ every current budget.P.Candle (from Meets)
lemma Candle.small {L' : Rep G (C.side i p)} (hx : i≤N) (h : Candle c i L' hx) : L'.p.threshold / anneals C c i ≤ torque (clim C.path.levels i) := by
  obtain ⟨σ,g,Λ,δ,w,he,hp⟩:= h.settle.proper
  let s:= clim C.path.levels i;let a:= Vac.Numbers.Hat s; let b:=torque s
  have hC:0<s:= zero_lt_one.trans (C.path.levels.fits.delayed _); have hf:0<a:=by unfold a Vac.Numbers.Hat; positivity
  have hg:= warmth C c hx; let r:=anneals C c i
  have ht : L'.beta*r^2=1:= by
    have hz:= c.pos i hx
    unfold r anneals; rw [inv_pow,Real.sq_sqrt hz.le,← h.settle.tied.coupling,mul_inv_cancel₀ hz.ne']
  have hV : a^2*s=1:= by unfold a Vac.Numbers.Hat; rw [inv_pow,Real.sq_sqrt hC.le,inv_mul_cancel₀ hC.ne']
  rw [h.threshold]; apply (div_le_iff₀ hg).mpr
  have hx : a ≤ 2*r:= by
    apply (le_of_pow_le_pow_left₀ two_ne_zero (show 0 ≤ 2*r by exact mul_nonneg (by norm_num) hg.le))
    apply le_of_mul_le_mul_right _ hC; calc
      _ = L'.beta * r^2:= hV.trans ht.symm
      _ ≤ (4*s)*r^2:= mul_le_mul_of_nonneg_right he.cap (sq_nonneg _)
      _ = _ := by ring
  change a* hot s≤ torque s*r
  unfold torque; linarith only [mul_le_mul_of_nonneg_right hx (show 0 ≤ hot s from (Real.exp_pos _).le), mul_nonneg (show 0≤r from hg.le) (show 0≤ hot s from Real.exp_pos _|>.le)]

-- use Torque' = torque(top). Flag across stretch accounted and collapse gain at final.
structure Faring (b : Purse) (s : ℝ) : Prop where
  -- b_hat threshold, low stamp probes absorb
  calm : 1 ≤ torque s
  inside : torque s ≤ knox s-1
  primers : Common.priced (torque s) (2*b.taylor) ≤ bill 1 s
  budget : b.L*Common.priced (torque s) 1 ≤ knox s
  transverse : b.L + b.sends s ≤ knox s
  lots : ∀ u ∈ Set.Icc (s/2) s, torque u ≤ torque s
  venue :
    let J:= b.era.coast
    4*(rentQ J.Q (load b.era)*Perch.bill (-6) s) ≤ Perch.bill (-4) s
  paper :
    let J:= b.era.coast
    4*(rentQ J.Q (load b.era)*grant (knox s) (b.sends s) (b.double s) (2*b.taylor)) ≤ b.demand s
  voice u : u∈ Set.Icc (s/2) s→
    let H:=b.era; let a:=H.coast; let l:=Paint.trib a.a u
    let y:=Perch.bill (-1) s
    Real.exp l* (Perch.gas a u)^2+2*Perch.bill (-2) s *rentQ a.Q (load H+1)≤y ∧
      (↑((walls u+walls u+1):ℕ):ℝ)^4*y ≤ 1∧ Real.exp y -1 ≤ 1

variable {A : Levels G}
lemma Racer.pos {b s h j} (H : Racer b s h) (hi : j≤h):
    b.epoch s j ≤ Perch.bill (1-(b.goal:ℝ)) s ∧ b.epoch s j ≤ Perch.bill (-4) s := by
  have hr : b.epoch s j ≤ Perch.bill (1-(b.goal:ℝ)) s:= by
    apply le_trans (mul_le_mul_of_nonneg_right ((pow_le_pow_right₀ b.running hi).trans H.log) (Real.exp_pos _).le); rw [sub_eq_add_neg]; exact (overlap ..).le
  exact ⟨hr,hr.trans (Glimmer.billed _ (by
    have hx : (6:ℝ) ≤ b.goal:= by exact_mod_cast b.tolerance
    linarith))⟩


-- numerical gates on this stall; HTwist existence before L.Est partial
end YM.Next.Rank.Tapes
