import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.WardPre
import YM.Next.WARD_BIN.Pennies

/-!
# Unit & orientation preparedness of a console, and creating Based WITH Page
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Disk
open Function Set Filter Matrix MeasureTheory Wilson Lattice RG Source Labels Bid Precision
    Supply Pressure WardBin Next.Foundations Extra.Histories Work.G08
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical

variable {G : Gauge} {n : Side} {d k l m N p i : ℕ} {R : Rep G n} {C : Family G} {o : Site n} {F : Labels.Frame G d}
    {c : ℝ} {H : History G} {K : Coefficient F n} (S : SectionData F) {B : Hol G} (h : S.Sound B)
    {W : Worth}









-- direction transports constant submode and costs never increase there. need true transfer to fix gauge/norm in B.
lemma compass {x y : F.Coeff} {r : ℝ} (hy : F.core y=0) (h : direction H W m F x y r 0) :
    r=0 ∧ F.core x=0 := by
  obtain ⟨hr,-,B,hB,he,h⟩ := h
  --no let
  have hz : F.core (vowel F (H.S.block m) y) = 0 := by rw [core_vowel,hy]; funext i; simp [vowel]
  refine ⟨le_antisymm (h.trans ?_) hr, ?_⟩
  · simp only [hz,Frame.coeffSize,Pi.zero_apply,norm_zero, Finset.sum_const_zero, mul_zero, add_zero]
    exact le_rfl
  simp only [hy,Frame.coeffSize,Pi.zero_apply,norm_zero,Finset.sum_const_zero, add_zero,mul_zero] at he
  rw [sub_eq_zero.mp (size_separates _ _ he), (hB _).2.2, hz,map_zero]





section Flow
variable (D : Console H p F) {d0 : ℕ}



-- Needed for page alignment on the pre-export trajectory. No campaign assumption, only one-block Console.Purchases and finite algebra of terminal Signed readout,
-- no hypothesis about actual Cost.woke, etc.
structure Earned (R : Finset Cover) (X : Gas.Pad (H.rep N p N).activities (H.rep N p N).p)
    (t : ℕ) (l : ℕ) (w : ℝ) (B : Hol G) (W : Worth) : Prop where
  seats i : i ≤ N → D.centers i=0
  addresses : D.rods N t=WardBin.footprint R 0
  includes i : 0 ∈ D.rods N i
  flows : D.Purchases l N N W S B
  spins v : let e := fun x : F.Coeff => (D.signal N (WardBin.pennies S X R 0 t x) l).x
            e (star v)=star (e v) ∧ ∀ g : Signed,e (F.act g.ortho v)=F.act g.ortho (e v)
-- a strengthened step-form of spins from intermediate purchases using genuine symmetrization not shown. `spins` is currently a FINITE label invoice,
-- at each N,p for the actual delivered flow choices. w included for manifests.

variable {P : Bay.Roads G}

structure Quay (H : History G) (d N p : ℕ) where
  pad : Gas.Pad (H.rep N p N).activities (H.rep N p N).p
  ink : ℕ
  flight : Console H p ((frames G).level d)

abbrev Tested (P : Bay.Roads G) (U : Quay H d N p) (r : ℕ) (W : Worth) :=
  Earned (localSection G d) U.flight (P.art d).cover U.pad U.ink r (H.levels.params N).columns (Next.Foundations.hol G) W

-- common program application for Based and Shelf.Purchases -- still no Volley estimates!
variable (Q : Quay H d N p)


end Flow
end YM.Further.PhysicalPeriodLimitF933.Disk
