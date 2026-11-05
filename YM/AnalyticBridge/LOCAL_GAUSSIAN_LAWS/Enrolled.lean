import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.PSeries
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FOUNDATIONS.SU2
import YM.Next.SCHEDULE.Dues
import YM.Push.CUTOFF_PROJECTORS.Equations
import YM.Push.FREE_RESOLVENT.Fold
import YM.Push.FREE_RESOLVENT.JetWindows
import YM.Push.FREE_RESOLVENT.SharedCells

/-!
# From issued large-period price to all periods of a cover Row

No exact sizes tested at low periods. Gap transfer uses
period-folding on genuine native addresses, preserving norm factors
(and this is why not using e.g. wrap in the other direction with a
potentially nonperiodic formula). Also define repeating-tree registry
for an actual constant choice with c≥3.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Current
open Function Filter Lattice Wilson RG Precision Exterior Tree Matrix
open Bid FreeResolvent Bloch Laurent Work.F08
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {c f : Side}

section GapTransfers
variable {I J α : Type} [Fintype I] [Fintype J] [AddGroup I] [AddGroup J]
lemma sum_push (f : I →+ J) (hf : Surjective f) (s : J→ℝ) :
    ∑ i, s (f i)=(Fintype.card f.ker:ℝ)*∑ j, s j := by
  rw [← Fintype.sum_fiberwise f (fun i => s (f i)),Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  let Y := {i // f i=j}
  let Z := f ⁻¹' {j}
  have hc : Fintype.card (↥Z)=Fintype.card f.ker := Fintype.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hf j)
  have he : Fintype.card Y=Fintype.card (↥Z) := Fintype.card_congr (Equiv.subtypeEquivRight (fun i => Iff.rfl))
  -- Fintype.sum_fiberwise supplies induced instances
  have hw (i : Y) : f i.val = j := i.property
  change (∑ i : Y, s (f i.val)) = _
  simp_rw [hw]
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  -- proof irrelevance of Fintype
  exact congr_arg (fun i : ℕ => (i:ℝ)*_) (he.trans hc)

variable {m n : Side}
variable [Fintype α]
lemma dot_push (g : Site m →+ Site n) (hf : Surjective g) (x y : Co n α → ℝ) :
    dotProduct (x ∘ Universal.overlay g) (y ∘ Universal.overlay g)=(Fintype.card g.ker:ℝ)*dotProduct x y := by
  unfold dotProduct; rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  have he := sum_push g hf fun i => ∑ j, x (i,j)*y (i,j)
  convert he using 3
  · rfl
  congr; exact Subsingleton.elim _ _

lemma cofinal_prices (P : Row α α) (hP : P.safe) (a : ℝ) (b : ℕ) (h : ∀ n : Side, b ≤ n.val → Gap (P.acts n) a) (n : Side) :
    Gap (P.acts n) a := by
  constructor; intro v
  let m : Side := ⟨(b+1)*n.val,Nat.mul_pos (Nat.zero_lt_succ _) n.pos⟩
  have hh : b ≤ m.val := le_trans (Nat.le_succ b) (Nat.le_mul_of_pos_right _ n.pos)
  obtain ⟨g,hg⟩ := Universal.modulo (m:=m) (n:=n) (by unfold m; simp)
  have he (x z) : g (x+wrap m z)=g x+wrap n z := by simp [hg]
  have ht : Surjective g := fun x => ⟨wrap m (lift x),(hg _).trans (wrap_lift x)⟩
  have hl := (h m hh).lower (v ∘ Universal.overlay g)
  rw [Universal.law P hP g he,dot_push g ht,dot_push g ht] at hl
  rw [mul_left_comm] at hl
  exact le_of_mul_le_mul_left hl (by exact_mod_cast Fintype.card_pos)
end GapTransfers

section Catalogue
variable (P : Patch) (K : KernelChoices)
-- use data shorthand (see Lifted; coarse n, fine n*L). Count c first
-- phase n arbitrary when assembling Prop registers.
abbrev nativeStep (n : Side) := Lifted.data (c:=n) (f:=n*P.L) (P:=P) rfl K

def three : Side := ⟨3,by norm_num⟩
variable (F : Forest (nativeStep P K three).ratio)
def spread {n : Side} : Forest (nativeStep P K n).ratio := Lifted.rebuild F (fun _ => 0) (show 3 ≤ three.val from le_rfl)

def picked (G : Gauge) (i : Co P.L (PAC G 1)) :=
  let g:=(nativeStep P K three).ratio
  (g.assemble (0,i.1),axisEquiv.symm i.2.1) ∉ F.trunks

def Asked (G : Gauge) := {i : Co P.L (PAC G 1) // picked P K F G i}
instance instAsked (G : Gauge) : Fintype (Asked P K F G) := inferInstanceAs (Fintype {_i : Co _ _ // _})
instance askedDecide (G : Gauge) : DecidableEq (Asked P K F G) := Classical.typeDecidableEq _
variable (G : Gauge)

lemma ballot (n : Side) (hn : 3 ≤ n.val) (y : Site n) (i : Co P.L (PAC G 1)) :
    (y,i) ∈ Set.range (Lifted.grid (nativeStep P K n) (spread P K F) (G:=G)) ↔ picked P K F G i := by
  obtain ⟨p,i⟩ := i
  exact (Lifted.assemble_test (G:=G) (nativeStep P K n) (spread P K F) y p i).trans (not_congr (Lifted.rebuild_at F (h':=(show (n*P.L).val=n.val*P.L.val from rfl)) (fun (_:Site n) => 0) y (show 3 ≤ three.val from le_rfl) hn p (axisEquiv.symm i.1)).symm)

variable {n : Side}


def footprint (i : Co n (Asked P K F G)) : Co n (Co P.L (PAC G 1)) := (i.1,i.2.val)


-- active -> registered residual

def link (hn : 3 ≤ n.val) : Active G (spread P K F (n:=n)) ≃ Co n (Asked P K F G) :=
  let Q := Lifted.grid (nativeStep P K n) (spread P K F) (G:=G)
  let f := fun i : Active G (spread P K F (n:=n)) => (((Q i).1,⟨(Q i).2, (ballot P K F G n hn (Q i).1 (Q i).2).mp ⟨i,rfl⟩⟩) : Co n (Asked P K F G))
  Equiv.ofBijective f ⟨fun i j h => Lifted.grid_inj _ _ (congr_arg (footprint P K F G (n:=n)) h),fun ⟨y,j⟩ => by
    obtain ⟨x,hx⟩ := (ballot P K F G n hn y j.val).mpr j.property
    have hz : (Q x).1=y := congr_arg Prod.fst hx
    exact ⟨x,Prod.ext hz (Subtype.ext (congr_arg Prod.snd hx))⟩⟩



def common (H : FaceRow) : Row (Asked P K F G) (Asked P K F G) :=
  fun i j => fullRow G P K.penalty H i.val j.val

lemma common_price {H : FaceRow} {s M : ℝ} (hs : 0 ≤ s) (hM : 0≤M) (he : H.strip s M) :
    (common P K F G H).strip s (outputPrice P K.penalty s M) := fun i j => fullRow_width P _ hs hM he i.val j.val

lemma enrolled (n : Side) (hn : 3 ≤ n.val) {H : FaceRow} {s M : ℝ} (hs : 0≤s) (h : H.strip s M) :
    treeMatrix G (nativeStep P K n) (spread P K F) H=((common P K F G H).acts n).submatrix (link P K F G hn) (link P K F G hn) := by
  ext i j
  let v := nativeStep P K n
  unfold treeMatrix; rw [fullRow_periods v hs h]
  simp only [Matrix.submatrix_apply]
  rfl
end Catalogue
end YM.AnalyticBridge.LocalGaussianLaws.Current
