import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Inverse
import YM.Next.EXTRACTION.Tails
import YM.Push.FREE_RESOLVENT.Costed

/-!
# The verified no-hole affine matrices ON actual group fields

Mirror FREE_RESOLVENT/Affine exactly (hence also its choice of channel:
PULL of whole prediction). This is not a chosen-sector D or an identified
stationary Hessian. Holds the tree, readout choices and path cuts fixed in
each derivative. Right below, prove equality of actual exponential chart
functions and obtain their forward data WITHOUT assuming a single inverse
jet. The centred tests HERE are at V=1, precisely the Taylor test at B=0;
the functions being differentiated still evaluate on actual Config at EACH
of the nested increments, not by additive proxy fields or a BCH cut theory.
Same harmonic and inactive coordinate convention as `primary`, `whole`
respectively. `Sheet` means the supplied exponential path sum test (can
weaken from real Bounds); need actual StepData with Bid.Larger. All this
uses fixed-L affine prices, no pre-L loop or schedule assertion.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.NoHole
open Lattice Wilson RG Function WardBin.Lies Exterior FreeResolvent Affine Mark TestD Window Tree Precision
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f}

def observed (S : StepData c f) (V : Config G c) (v : Vec G f 1) := increment (replica S.ratio V) (paint G f v)

def faceRow (S : StepData c f) (s : Signed) (V : Config G c) (v : Vec G f 1) : Vec G f 2 := fun e =>
  G.curvature (faceValue (pull s 0 (observed S V v)) (e.1,plaqEquiv.symm e.2.1)) e.2.2

def predictRow (S : StepData c f) (s : Signed) (k : S.Choices) (V : Config G c) (v : Vec G f 1) : Vec G c 1 := fun i =>
  G.projectColor (G.mat (pull s 0 (S.prediction (observed S V v) k) (edge i) *
    ((pull s 0 (S.prediction (replica S.ratio V) k)) (edge i))⁻¹)) i.2.2

def pathRows (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) (V : Config G c) : Matrix (tile G f) (tile G f) ℝ :=
  Matrix.of fun i j => ∑' q, let p := W.row (plaqEquiv.symm i.2.1) q; if r p.2 then
    p.1 * element (pull s 0 (replica S.ratio V)) i j p.2 else 0

def screen (S : StepData c f) (s : Signed) (k : S.Choices) (p : Clip) (W : PathData G) (r : Admit) (V : Config G c) :=
  let H := LinearMap.toMatrix' (fderiv ℝ (faceRow S s V) 0).toLinearMap
  let Q := LinearMap.toMatrix' (fderiv ℝ (predictRow S s k V) 0).toLinearMap
  p.direct • squareQ H + squareQ (pathRows S s W r V * H) + S.kernel.penalty • squareQ Q

def stack (S : StepData c f) (t : S.Choices) (p : Clip) (W : PathData G) (r : Admit) (V : Config G c) :=
  (Fintype.card Signed : ℝ)⁻¹ • (∑ s, screen S s t p W r V)



def paddedGram (S : StepData c f) (t : S.Choices) (p : Clip) (W : PathData G) (r : Admit) (T : Forest S.ratio) (V : Config G c) :=
  Shell.pad (freeTo G S T) (stack S t p W r V)

variable (t : S.Choices) (p : Clip) (T : Forest S.ratio) {W : PathData G} (r : Admit) (k : ℕ)





variable {σ M : ℝ} (hs : 0 < σ) (hm : 0 ≤ M) (hW : Sheet W σ M) (he : Bid.Larger (G:=G) S)
include hs hm hW he



lemma padded_data :
    let d := width G S.patch S.kernel p k M σ
    Data (native c) (home S) Prod.fst k (tier σ k/2) (nuts G S.patch S.kernel p k M σ) (gum G S.patch S.kernel p) d 1
      (paddedGram S t p W r T) 1 := by
  intro d
  let F := crest S t (T:=T) (U:=T) (W:=W) (p:=p) r
  have hF := mast (p:=p) (T:=T) (U:=T) (v:=0) (n:=k) S t hs hm hW he (fun _ _ => Iff.rfl) r (Set.left_mem_Icc.mpr zero_le_one)
  have hp := gauged G S.patch S.kernel p k hs hm
  have h := (restricted 0 (hF.bundle hp.m le_rfl)).glue (B:=over (paddedGram S t p W r T) 1) (Filter.Eventually.of_forall (fun z => now ..))
  refine ⟨h.smooth, ?_, ?_, fun l _ hl => by rw [mul_one]; exact h.bound l hl⟩
  · have he : F (0,0)=over (paddedGram S t p W r T) 1 0 := now ..
    rw [← he]; exact hF.gap
  have hh := h.bound [] (by simp); rw [zeroth] at hh; exact hh.reclaim
end YM.SelectedOrderedKernels.NoHole
