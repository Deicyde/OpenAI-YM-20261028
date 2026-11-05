import YM.RG08.Carrel.Nest
import YM.Extra.ITERATION_NO_LOSS.Atoms
import YM.Work.F03.Transport
import YM.Work.F05.Actions
import YM.RG08.Rudder.Sym.Lien

/-! # Charges of the canonical invariant completion; absolute true path budgets.
No phases, includes 4 per curvature chord and all axes work.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Carrel
open Lattice Laurent Forms Pert.Bulk Isles Packets Glyph Filter Finset Function RG
open Rudder.Symmetry Wilson Exterior
open scoped BigOperators Topology Classical ENNReal
variable {G:Gauge}{n:ℕ}{P:Side}
abbrev Rayk (G:Gauge)(r:ℕ):=Anchor.Kind G.ColorIndex r
abbrev Coord := Tape n (Cover × TypeFace 2)
variable (F:Flake n (Market (Rayk G 2)))

def join (x:Coord (n:=n))(y:Tape n G.ColorIndex):Slide (Rayk G 2) n:=fun i=>((x i).1,(x i).2,y i)
def light (F:Flake n (Market (Rayk G 2)))(x:Coord (n:=n)):Urn G.ColorIndex n:=fun y=>F (join x y)
def lamp (F:Flake n (Market (Rayk G 2))):Prop:=∀ x,light F x∈dressed G n
lemma compressed (F:Rudder.Raw G.ColorIndex n)(h:hue (dressed G n) F):lamp (Anchor.compress 2 F):=by
 intro x; exact h (fun i=>((x i).1,(x i).2.1))

def base (o:Fin n)(x:Coord (n:=n)):Prop:=(x o).1=0
def deposit (o:Fin n)(x:Coord (n:=n)):Atom G n where
 leg i:=Extra.Iteration.slot (x i).1 (plaqEquiv.symm (x i).2)
 coeff := fun y=>neck o F (join x y)
lemma lit (h:lamp F)(o x): (deposit F o x).Invariant:=by
 intro u X
 by_cases hz:base o x
 · have hh:(deposit F o x).coeff=light F x:=by ext y; exact if_pos hz
   simp only [Atom.poly,hh];exact (h x).1 u X -- Vmem carrier reduce? Invalid projection
 have hh:(deposit F o x).coeff=(0:Urn G.ColorIndex n):=by ext y; exact if_neg hz
 simp [Atom.poly,hh]

lemma legcost (o:Fin n)(x:Coord (n:=n)):(deposit F o x).length=(∑ i,Laurent.size (x i).1)+4*n:=by
 simp [deposit,Atom.length,Extra.Iteration.slot_length,Finset.sum_add_distrib,Nat.mul_comm]

private def prism (G:Gauge)(n:ℕ) : Coord (n:=n) × Tape n G.ColorIndex ≃ Slide (Rayk G 2) n where
 toFun z:=join z.1 z.2
 invFun x:=((fun i=>((x i).1,(x i).2.1)),(fun i=>(x i).2.2))
 left_inv _:=rfl
 right_inv _:=rfl

lemma paid {σ p:ℝ}(o:Fin n)(hσ:0<σ)(hp:0≤p)(h:Held (carpet (Rayk G 2)) σ p F):
  let α:=σ/(n:ℝ)
  Extra.Iteration.Charged (deposit F o) α ((Real.exp (α*(4*n:ℕ)) * (Fintype.card (Rayk G 2):ℝ))*p):=by
  let α:=σ/(n:ℝ)
  intro
  let i:=deposit F o
  let c:=Real.exp (α * (4*n:ℕ))
  have hc:0≤c:=(Real.exp_pos _).le
  let C:=((Fintype.card (Rayk G 2):ℝ)*p)
  have hC:0≤C:=mul_nonneg (Nat.cast_nonneg _) hp
  let U:=neck o F
  let a(z:Slide (Rayk G 2) n):=|U z| * Real.exp (σ*shelf z)
  have hr : Won U σ C := sensible o h hp
  have hn:0<n:=o.pos
  have hL(x:Coord (n:=n))(y:Tape n G.ColorIndex)(hz:base o x):
      (i x).budget α ≤ ((i x).magnitude*c)*Real.exp (σ*shelf (join x y)):=by
    unfold Atom.budget
    rw [mul_assoc,←Real.exp_add]; unfold i; rw [legcost F]
    apply mul_le_mul_of_nonneg_left _ (by unfold Atom.magnitude;positivity)
    apply Real.exp_le_exp.mpr
    have ht(k:Fin n): (size (x k).1:ℝ) ≤ shelf (join x y):=by
       rw [shelf_diam]
       have he:=Ground.le_radius (carpet (Rayk G 2)) (join x y) k o
       change Laurent.size ((x k).1-(x o).1) ≤ (_:ℝ) at he
       simpa only [show (x o).1=0 from hz,sub_zero] using he
    have he : (∑ k:Fin n,(size (x k).1:ℝ)) ≤ n*shelf (join x y):=by simpa using Finset.sum_le_sum (s:=univ) (fun k _=>ht k)
    push_cast; rw [mul_add];unfold α at *
    field_simp -- inspect
    have hh:=mul_le_mul_of_nonneg_left he hσ.le
    linarith
  -- actually need termwise equality of magnitudes with a regardless y, shelf independent y
  have hx(u:Coord (n:=n))(v w:Tape n G.ColorIndex):shelf (join u v)=shelf (join u w):=rfl
  have hi (u:Coord (n:=n)): (i u).budget α ≤ c * ∑ y:Tape n G.ColorIndex, a (join u y):=by
    by_cases ht:Nonempty (Tape n G.ColorIndex)
    · by_cases hh:base o u
      · let v:= Classical.choice ht
        apply (hL u v hh).trans_eq
        unfold Atom.magnitude;rw [Finset.sum_mul,Finset.sum_mul,Finset.mul_sum];apply Finset.sum_congr rfl;intro y _
        unfold i deposit;rw [hx u v y]; unfold a U;ring
      have hm:(i u).coeff=0:=by ext y;exact if_neg hh
      exact (by simp only [Atom.budget,Atom.magnitude,hm,Pi.zero_apply,abs_zero,sum_const_zero,zero_mul];unfold a c;positivity)
    letI : IsEmpty (Tape n G.ColorIndex):=not_nonempty_iff.mp ht
    simp [Atom.budget,Atom.magnitude]
  -- charge real budgets from Won real vs ENN
  have he : Summable a:=bill_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hr.2)
  have ht : ∑' z,a z ≤ C := by
    apply (ENNReal.ofReal_le_ofReal_iff hC).mp
    rw [ENNReal.ofReal_tsum_of_nonneg (fun z=>show 0≤a z from by unfold a; positivity) he];exact hr.2
  let s:=prism G n
  have ha:= s.summable_iff.mpr he
  have ha':Summable (fun (u:Coord (n:=n))=> c*∑ y:Tape n G.ColorIndex,a (join u y)):=by
     have hh:= ha.prod
     simpa [tsum_fintype,s,prism] using hh.mul_left c
  have hv u :0≤(i u).budget α:=by unfold Atom.budget Atom.magnitude; positivity
  have hf:=ha'.of_nonneg_of_le hv hi
  refine ⟨hv,hf,(hf.tsum_le_tsum hi ha').trans ?_⟩
  rw [tsum_mul_left]
  change _≤c*(Fintype.card (Rayk G 2):ℝ)*p
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hc
  have hh:∑' u:Coord (n:=n),∑ y:Tape n G.ColorIndex,a (join u y)=∑' z,a z:=by
     rw [← s.tsum_eq a,show (∑' (c:Coord (n:=n) × Tape n G.ColorIndex), a (s c))=∑' u,∑' y:Tape n G.ColorIndex,a (s (u,y)) from ha.tsum_prod];simp_rw [tsum_fintype];rfl
  rw [hh];exact ht

end YM.RG08.Carrel
