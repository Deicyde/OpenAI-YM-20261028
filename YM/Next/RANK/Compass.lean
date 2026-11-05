import YM.Next.RANK.Bird
import YM.Next.RANK.BoundParticle
import YM.Next.RANK.Sky

/-!
# E full-kernel polynomial recursion

One atlas for the requirements under study at that N,p,k. Finite arrays
in canonical positive-face coordinates. All contractions finite; before integration, formal algebra, leave its comparison to actual
Wilson push densities as *estimate gate*. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Atlas
open Function Lattice Wilson RG Perch  Beamer Normal Configuration  CellsInt Rise MvPolynomial Marker Glyph Exponential Particle
open scoped Topology BigOperators Classical

variable {G : Gauge} {P : Schedule} {p k l n : ℕ}

-- Actual finite colors at a level, same period
abbrev Chamber (G : Gauge) (P : Schedule) (i p : ℕ) := Site (P.side i p) × PlaqAxes × G.ColorIndex

def body (x : Cover) (i : Address G) : Chamber G P k p := (wrap _ (x+i.1),i.2)

-- possibly complex (projection uses explicitly real equality for samples below). No free F entries here.
structure AtlasData (G : Gauge) (P : Schedule) (p : ℕ) where
  /-- Slots for two-point kernels κ of this marker comparison. RRack etc w/new
  estimates would need actually supply suitable arrays *prior to* extrapolating
  W. Not presupposing stationarity or positivity; significance of these is via
  tests (including Atlas in Step vs curvature variables in principal tag laws).
  Does not track this data as part of Family, impose any unasserted relationship
  to physical metric choices, require a particular algorithm for claiming stamps,
  or obtain any C/Y or Wχ existence. -/
  κ i : Normal.Symmetric (Chamber G P i p)
  -- factor Q-P_comp for one step from i+1 to i.
  path i : Chamber G P (i+1) p → Chamber G P i p →₀ ℂ

variable (X : AtlasData G P p)

def stageCov (i : ℕ) : Normal.Symmetric (Chamber G P (i+1) p) := X.κ (i+1)+ -(scope (X.path i) (X.κ i))

-- H-at-step ≤ heights determined by E schedule, not overwritten W.

def preserve (C : Normal.poly (Chamber G P k p)) (w : ℕ) (hw : w ≤ k) : Normal.poly (Chamber G P w p) :=
    Nat.decreasingInduction (motive := fun i _ => Normal.poly (Chamber G P i p))
      (fun i _ t => pipe (X.path i) (stageCov X i) t) C hw

def lines (j) {k : ℕ} (hj : j≤k) : Chamber G P k p → Chamber G P j p →₀ ℂ :=
    Nat.decreasingInduction (motive := fun l _ => Chamber G P k p → Chamber G P l p →₀ ℂ) (fun i _ H z => Finsupp.linearCombination ℂ (X.path i) (H z))
      (fun i => Finsupp.single i 1) hj

def blush (j) (hj : j≤k) := X.κ k + - Normal.scope (lines X j hj) (X.κ j)

lemma wish {k} (p' : ℕ) (X : AtlasData G P p') (q : Normal.Symmetric (Chamber G P k p')) : scope (lines X k le_rfl) q=q := by
  apply Normal.Symmetric.ext; funext i j
  have he : lines X (k:=k) k le_rfl = _ := Nat.decreasingInduction_self ..
  unfold lines; rw [Nat.decreasingInduction_self]; exact match_name id q i j
lemma cancels (h : l<k) : scope (lines X (l+1) (show l+1≤k from h)) (stageCov X l)+ blush X (l+1) (show l+1≤k from h)=blush X l h.le := by
  let H := lines X (l+1) (show l+1≤k from h)
  let V := Normal.scope (X.path l) (X.κ l)
  have ht {A : Type} (v w : Normal.Symmetric A) (a b : A →₀ ℂ) : treats (v + -w) a b=treats v a b-treats w a b := by
    unfold treats; change Finsupp.linearCombination ℂ (Finsupp.linearCombination ℂ (v.cov+ -w.cov) a) b=_
    simp only [Finsupp.linearCombination_apply,Finsupp.sum,Finset.sum_apply, Pi.add_apply,Pi.smul_apply,Pi.neg_apply, smul_eq_mul,mul_add,mul_neg, sub_eq_add_neg]
    simp only [Finset.sum_add_distrib,mul_add,mul_neg,Finset.sum_neg_distrib]
  have hx : lines X (k:=k) l h.le=fun i => Finsupp.linearCombination ℂ (X.path l) (H i) := Nat.decreasingInduction_succ_left ..
  apply Normal.Symmetric.ext
  funext i j; unfold blush; rw [hx,Normal.scopes]
  change treats (X.κ _ + - V) _ _ + ((X.κ k).cov _ _+- treats (X.κ _) (H i) (H j))=(X.κ k).cov _ _+ - treats V (H i) (H j)
  rw [ht]; rw [sub_eq_add_neg]; change treats (X.κ (l+1)) (H i) (H j) + _ + _ = _; abel

lemma preserves (w : ℕ) (hw : w ≤ k) (C) : preserve X C w hw=pipe (lines X w hw) (blush X w hw) C := by
  induction hw using Nat.decreasingInduction with
  | self =>
    rw [preserve,Nat.decreasingInduction_self,pipes,blush,wish,Normal.Symmetric.cancels,froze,lines,Nat.decreasingInduction_self]
    suffices exchange (fun i : Chamber G P k p => Finsupp.single i 1)=AlgHom.id ℂ (Normal.poly _) by rw [this,AlgHom.id_apply]
    ext1 i; simp
  | of_succ i hi IH =>
    have he : lines X (k:=k) i hi.le = fun j => Finsupp.linearCombination ℂ (X.path i) (lines X (i+1) hi j) := Nat.decreasingInduction_succ_left ..
    rw [show preserve X C i hi.le=pipe (X.path i) (stageCov X i) (preserve X C (i+1) hi) from Nat.decreasingInduction_succ_left ..,IH,piped,cancels X hi,he]

lemma detached (p : ℕ) (hw : p ≤ k) (C) (m : Chamber G P p _→ℂ) :
    MvPolynomial.aeval m (preserve X C p hw) = blend (blush X p hw) (reads (lines X p hw) m) C := by rw [preserves,pipes,reads_val]; rfl

-- W support at k cutoff offset, all a priori stencil addresses relative to its insertion origin

def strip (B : ℕ) (G : Gauge) := ((Lattice.box B) ×ˢ (Finset.univ (α:=PlaqAxes × G.ColorIndex))).filter fun x : Address G => street x.1 ≤ B
@[simp] lemma tracing (B : ℕ) (x : Address G) : x∈strip B G ↔ street x.1 ≤ B := by
  rw [strip,Finset.mem_filter]; refine ⟨And.right,fun h => ⟨?_,h⟩⟩
  simp only [Finset.mem_product,Finset.mem_univ,and_true,box_test]
  have ht (i : Axis) : (x.1 i).natAbs≤B := (Finset.single_le_sum (fun i _ => show 0 ≤ (x.1 i).natAbs from Nat.zero_le _) (Finset.mem_univ i)).trans h
  exact ⟨fun i => by have := ht i; omega,fun i => by have:= ht i; omega⟩

abbrev trimV (B : ℕ) (G : Gauge) := ↥(strip B G)
variable {B : ℕ}

-- wake/read for all positions. This M can still depend on C.p,N path. Need estimates.

def control (x : Cover) (B : ℕ) := Normal.scope (fun i : trimV B G => Finsupp.single (body (k:=k) x i.val) 1) (X.κ k)

def Qmarks (v : Fin n→ Cover) (h : l ≤ k) : Normal.Symmetric (Fin n × Address G) :=
    let f := fun i : Fin n × Address G => body (k:=k) (P:=P) (p:=p) (v i.1) i.2
    scope (fun i => Finsupp.single (f i) 1) (blush X l h)+ -(self (fun i => scope (fun x : Address G => Finsupp.single (body (v i) x) 1) (X.κ k)))

def noise (v : Fin n → Cover) (h : l ≤ k) (m : Chamber G P l p → ℂ) : Fin n × Address G → ℂ := fun i =>
    reads (lines X l h) m (body (v i.1) i.2)

/-- Polynomial moment at all these formal kernels with K footprint. `P₀` already in
normal coefficient units (milk - to get bare polynomial). Keep exact operators.
W approximation uses the *constant-free log of this whole glyph*.
No labels null-read assumption here. -/
def Answer (w : Fin n→ Cover) (h : l ≤ k) (P₀ : Fin n→Normal.poly (trimV B G)) (m : Chamber G P l p→ℂ) : veil (Fin n) :=
    Poly.inject fun T=>
      MvPolynomial.aeval m (preserve X (∏ i∈ T.val, MvPolynomial.rename (fun z : trimV B G => body (w i) z.val)
        (milk (-(control X (k:=k) (w i) B)) (P₀ i))) l h)

lemma Answer_part (w : Fin n→ Cover) (h : l≤k) (P₀ : Fin n → Normal.poly (trimV B G)) (m : Chamber G P l p→ℂ)
    (T : modes (Fin n)) :
    let f := fun z : Fin n × trimV B G => (z.1,z.2.val)
    (Answer X w h P₀ m).part T = blend (scope (fun i => Finsupp.single (f i) 1) (Qmarks X w h)) ((noise X w h m) ∘ f) (pot T.val P₀) := by
  intro f
  unfold Answer; change aeval _ _=_; rw [detached]
  let v := fun i (x : trimV B G) => Finsupp.single (body (P:=P) (k:=k) (p:=p) (w i) x.val) (1:ℂ)
  simp_rw [labelled]; rw [Normal.lodge v (fun i => control X (k:=k) (w i) B)]
  let A := blush X l h
  have hm : reads (fun z : Fin n × trimV B G => v z.1 z.2) (reads (lines X l h) m)=((noise X w h m) ∘ f) := by
    funext z; unfold reads; simp only [v,Finsupp.linearCombination_single,one_smul]; rfl
  dsimp only; rw [hm]
  let L := fun z : Fin n × trimV B G => v z.1 z.2
  let R := fun i => control X (k:=k) (w i) B
  let W := scope L A+ -(self R)
  have hu : W = scope (fun i => Finsupp.single (f i) 1) (Qmarks X w h) := by
    apply Normal.Symmetric.ext; funext i j
    rcases i with ⟨i,x⟩; rcases j with ⟨j,y⟩
    rw [Normal.match_name f]
    change (scope L A).cov (i,x) (j,y) + -(if i=j then _ else 0) = (scope _ A).cov _ _ + -(if i=j then _ else 0)
    have ht : (scope L A).cov (i,x) (j,y) = A.cov (body (w i) x.val) (body (w j) y.val) := match_name (fun (z : Fin n × trimV B G) => body (w z.1) z.2.val) A _ _
    rw [ht];
    let g := fun z : Fin n × Address G => body (p:=p) (k:=k) (P:=P) (w z.1) z.2
    rw [Normal.match_name g A]
    split_ifs <;> rfl
  exact congr_arg (fun p => blend p _ (pot T.val P₀)) hu

lemma phased (w : Fin n→Cover) (h : l≤k) (P : Fin n→ Normal.poly (trimV B G)) (m) : (Answer X w h P m).part (quiet _)=1 := by
  rw [Answer_part]; exact fresh ..
end YM.Next.Rank.Atlas
