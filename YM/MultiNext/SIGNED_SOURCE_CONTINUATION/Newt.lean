import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Pattern
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Strings


set_option warningAsError false

/-!
#  signed offsets: exact difference recursion

Implement E Newton approximation via ALL-axis recursion (no enumeration
of multi-indices). About the cover origin 0 after recenter so read positions
and tally shifts in the true `Laurent` convention, not positive shifts only.
No operator or Fourier assumptions here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Newt
open Lattice Wilson RG Finset Function Set MeasureTheory Laurent
open Powers Pattern
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def jump (f : Cover→E) (i : Axis) (x : Cover) := f (x+Lattice.step i)-f x
omit [NormedSpace ℝ E] in
lemma commute (f : Cover→E) (i j : Axis) : jump (jump f i) j=jump (jump f j) i := by
  funext y; unfold jump; rw [add_right_comm y (Lattice.step j)]; abel

def piece : ℕ → (Cover→E) → E4 → E
| 0,p,_ => p 0
| k+1,p,x => ((k:ℝ)+1)⁻¹ • ∑ i:Axis,x i • piece k (jump p i) (x-basis i)

lemma ix (p : Cover→E) (k : ℕ) (x : E4) (i : Axis) : piece (k+1) p (x+basis i)-piece (k+1) p x=piece k (jump p i) x := by
  induction k generalizing p x i with
  | zero =>
    simp only [piece, Nat.cast_zero,zero_add, inv_one, one_smul,PiLp.add_apply,add_smul,Finset.sum_add_distrib, add_sub_cancel_left]
    simp [basis,ite_smul]
  | succ k ih =>
    have hh (v : Axis) : piece (k+1) (jump p v) (x+basis i-basis v)-piece (k+1) (jump p v) (x-basis v) =
        piece k (jump (jump p i) v) (x-basis v) := by rw [show x+basis i-basis v=x-basis v + basis i from by abel,ih,commute]
    let c := ((k+1:ℕ):ℝ)
    let h := c+1
    have hc : 0 < c := by unfold c; positivity
    have he : 0 < h := by unfold h; positivity
    change h⁻¹ • (∑ v,(x+basis i) v • piece (k+1) (jump p v) _) - h⁻¹ • (∑ v,x v • piece (k+1) (jump p v) _) = _
    rw [← smul_sub]; simp only [PiLp.add_apply,add_smul,Finset.sum_add_distrib]
    rw [show (∑ v,(basis i) v • piece (k+1) (jump p v) (x+basis i-basis v))=piece (k+1) (jump p i) x by simp [basis,ite_smul]]
    let a v := piece (k+1) (jump p v) (x+basis i-basis v)
    let b v := piece (k+1) (jump p v) (x-basis v)
    let F := ∑ v,x v • piece k (jump (jump p i) v) (x-basis v)
    have he' : (∑ v,x v • a v) - ∑ v,x v • b v=F := by unfold F; rw [← Finset.sum_sub_distrib]; simp_rw [←smul_sub,a,b,hh]
    let M := piece (k+1) (jump p i) x
    change h⁻¹ • ((∑ v,x v • a v)+M-∑ v,x v • b v)=M; rw [show M=c⁻¹ • F by unfold M c; rw [piece]; push_cast; rfl] -- not match M
    rw [add_sub_right_comm, he']
    rw [smul_add,smul_smul,← add_smul]
    apply congrArg (· • F); unfold h; field_simp

lemma housed [FiniteDimensional ℝ E] (p : Cover→E) (k : ℕ) : piece k p∈Powers.space E4 E k := by
  induction k generalizing p with
  | zero => exact Powers.constants (p 0) 0
  | succ k ih =>
    let A := (ContinuousLinearMap.lsmul ℝ ℝ (E:=E)) -- type
    refine Powers.smul (Powers.sums Finset.univ (fun i x => x i • piece k (jump p i) (x-basis i)) (k:=k+1) fun i _ => ?_) _
    rw [add_comm k]
    have hp : (fun p : E4 => p i)∈Powers.space E4 ℝ 1 := Powers.residence (k:=1)
      ⟨(show ContDiff ℝ ω ⇑(EuclideanSpace.proj i : E4 →L[ℝ] ℝ) from ContinuousLinearMap.contDiff _), fun t v => by simp⟩ le_rfl
    let w (x : E4) := piece k (jump p i) x
    have hx : (fun x : E4 => w (x-basis i))∈Powers.space E4 E k := by
      have hW : w∈Powers.space E4 E k := ih _
      convert Powers.add (Powers.widen _ _ (Nat.sub_le k 1) (Powers.discrete (-basis i) hW)) hW using 1
      funext x; simp [sub_eq_add_neg]
    exact Powers.genie A hp hx

def take (k : ℕ) (f : Cover→E) (x : Cover) := ∑ i∈Finset.range k,piece i f (xyz x)
def tail (k : ℕ) (f : Cover→E) (x : Cover) := f x - take k f x
lemma base (f : Cover→E) (k : ℕ) : piece (k+1) f 0 = 0 := by simp [piece]
lemma top (k : ℕ) (f : Cover→E) : tail (k+1) f 0=0 := by
  rw [tail,take,Finset.sum_range_succ']; have hh : xyz 0 = 0 := by ext; simp [xyz]
  simp_rw [hh,base]; simp [piece]
lemma currency (k : ℕ) (f : Cover→E) (i : Axis) : jump (tail (k+1) f) i=tail k (jump f i) := by
  funext x
  change f (x+step i)-take (k+1) f (x+step i) - (f x-take (k+1) f x)=tail k (jump f i) x
  unfold tail take
  rw [xyz_step, Finset.sum_range_succ', Finset.sum_range_succ']
  have h : (∑ b∈Finset.range k,piece (b+1) f (xyz x+basis i)) - (∑ b∈Finset.range k,piece (b+1) f (xyz x)) =
      ∑ b∈Finset.range k,piece b (jump f i) (xyz x) := by rw [←Finset.sum_sub_distrib]; exact sum_congr rfl fun b _ => ix ..
  have hh (x) : piece 0 f x=f 0 := rfl
  rw [←h]; simp only [hh,jump]; abel
end YM.MultiNext.SignedSource.Newt
