import YM.Ac.Table
import YM.Next.WARD_BIN.Eqs
import YM.Next.WARD_BIN.Lies
import YM.Pressure.Seeds




/-!
# One-mark arithmetic in the chart / alphabet of a step

Subtract actual entries at common addresses using unmasked differentiability.
Pay signed remainders at same κ and supports. Exact density algebra independent
of origin choice; for descendants on a history will also need the direction
lemma FROM the single-step engine.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Filter Set MeasureTheory Lattice Wilson RG Source Source.Drops Bid Work.G07 
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {m d i N p : ℕ} {F : Labels.Frame G d}
    {H : Hol G} {R : Rep G n} {o : Site n}

abbrev Baton (F : Labels.Frame G d) (n : Side) := F.Coeff ×
  (ℕ → Config G n → ℂ) × (ℕ → Config G n → ℂ)
abbrev Stripe (n : Side) := ℕ → Support n

def raw (P : Coefficient F n) : Baton F n := ⟨P.x,P.regular,P.forced⟩
def castAt (a : Stripe n) (x : Baton F n) : Coefficient F n := ⟨x.1,a,x.2.1,x.2.2⟩


@[simp] lemma from_castAt (a : Stripe n) (x : Baton F n) : raw (castAt a x)=x := rfl

def stepLess (P Q : Coefficient F n) := castAt P.support (raw P-raw Q)

lemma sub_funded {P Q : Coefficient F n} (hp : P.support=Q.support) (hx : P.Format o H R) (hy : Q.Format o H R) :
    (stepLess P Q).Format o H R := by
  constructor
  · intro i; exact Lies.regsub (hx.smooth i) (show R.p.Regular (P.support i) (Q.regular i) from hp.symm ▸ hy.smooth i)
  · exact hx.origin
  · intro i; change P.regular i 1-Q.regular i 1=_; rw [hx.identity_null,hy.identity_null,sub_zero]
  · intro i hi j
    obtain ⟨hc,h⟩ := hx.projects i hi j
    obtain ⟨he,e⟩ := hy.projects i (hp ▸ show Nonwrapping (P.support i) o from hi) j
    refine ⟨hc.sub he, fun k hk => ?_⟩
    have hh : (k : ℕ∞ω) ≤ (d : ℕ∞) := by exact_mod_cast hk
    change iteratedDeriv k (fun t => P.regular i _-Q.regular i _) 0=0
    rw [iteratedDeriv_fun_sub (hc.of_le hh) (he.of_le hh), h k hk,e k hk,sub_zero]
  · intro i U H
    by_cases ht : P.forced i U=0
    · exact hy.forcing i U fun e => H (show P.forced i U-Q.forced i U=0 by rw [ht,e,sub_zero])
    exact hx.forcing i U ht
  · intro i hi; by_cases he : P.forced i=0
    · exact hy.carried i (fun hg => hi (show P.forced i-Q.forced i=0 by rw [he,hg,sub_zero]))
    exact hx.carried i he
  · intro i k U; exact congr_arg₂ (·-·) (hx.invariant i k U) (hy.invariant i k U)
  · intro i U V he h; exact congr_arg₂ (·-·) (hx.supported i U V he h) (hy.supported i U V he h)
  intro i; exact (hx.borel i).sub (hy.borel i)

lemma mass_add {f g : ℕ → ℝ} {X : Stripe n} {A B : ℝ} {p : BudgetPoint}
    (h : SumBudget (fun i => p.mass (X i) (f i)) A) (hh : SumBudget (fun i => p.mass (X i) (g i)) B) :
    SumBudget (fun i => p.mass (X i) (f i+g i)) (A+B) := by
  have he (i) : p.mass (X i) (f i+g i)=p.mass (X i) (f i)+p.mass (X i) (g i) := mul_add ..
  simp_rw [he]; exact ⟨fun i => add_nonneg (h.1 i) (hh.1 i), h.2.1.add hh.2.1,
    (h.2.1.tsum_add hh.2.1).trans_le (add_le_add h.2.2 hh.2.2)⟩

lemma sub_rem {P Q : Coefficient F n} (hp : P.support=Q.support) (hx : P.Format o H R) (hy : Q.Format o H R)
    {k a b : ℝ} (ha : P.remBound o R k a) (hb : Q.remBound o R k b) :
    (stepLess P Q).remBound o R k (a+b) := by
  obtain ⟨a1,b1,ha1,hb1,hbA,hk, ⟨q,hq,H⟩, ⟨s,hs,S⟩⟩ := ha
  obtain ⟨a2,b2,ha2,hb2,hbB,_, ⟨r,hr,H'⟩,⟨t,ht,T⟩⟩ := hb
  refine ⟨a1+a2,b1+b2,add_nonneg ha1 ha2,add_nonneg hb1 hb2,by linarith,hk,⟨q+r,?_,fun i => ?_⟩,
    ⟨s+t,by rw [mul_add]; exact mass_add hs ht,fun i => ?_⟩⟩
  · exact mass_add hq (hp.symm ▸ hr)
  · have he := hy.smooth i; rw [← hp] at he H'
    exact Lies.pays_sub (hx.smooth i) he (H i) (H' i)
  exact ⟨add_nonneg (S i).1 (T i).1,fun U => (norm_sub_le ..).trans (add_le_add ((S i).2 U) ((T i).2 U))⟩

lemma rem_nonneg {P : Coefficient F n} {c b : ℝ} (h : P.remBound o R c b) : 0≤b := by
  obtain ⟨x,y,hx,hy,h,-⟩ := h; exact (add_nonneg hx hy).trans h

-- accounting for subtractions at common addresses





end YM.WardBin
