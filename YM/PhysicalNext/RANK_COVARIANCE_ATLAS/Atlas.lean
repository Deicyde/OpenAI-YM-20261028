import YM.Further.CORRECTED_LIFT_COEFFICIENTS.FacePrice
import YM.Next.FREE_KERNELS.Current
import YM.Next.FREE_KERNELS.Rack
import YM.Next.RANK.Compass
import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Scalar
import YM.Push.FREE_RESOLVENT.Flat



/-!
# One atlas, not a chosen approximant

Built from Levels/Steps + cutoff N: `location` is the actual Train of those
steps (all smoothing/factor indices in Levels), and `destination` gives the
step with that predecessor.

Keep it when assuming comparison inputs below.

More history matching will be needed e.g. to `ShapePort` and the unmasked
metric/Tower/path generators at these exact N,i.

Padding (i>N) is not used as
history.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.RankCovariance
open Function Lattice Laurent Bloch Exterior Matrix Precision Next.Free
open Further.FreeCovariance.KP
open RG FreeResolvent
open Next.Rank Next.Rank.Atlas
open scoped Topology BigOperators ComplexConjugate Classical

variable {n c f : Side} {G : Gauge}

/-- Cutting open the proof API. `Incidence` is exactly the atlas Chamber at a
side. Row starts at the base corner; can't symmetrize this with negative faces
at the same input link without translating. -/
abbrev Incidence (G : Gauge) (n : Side) := Site n × PlaqAxes × G.ColorIndex

def toPAC : Incidence G n ≃ Slot G n 2 :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr plaqEquiv (Equiv.refl _))




/-- Cast from a real symmetric tensor; no conjugation at the second endpoint. -/
def toNormal {m : Type*} (B : Matrix m m ℝ) (h : Bᵀ=B) : Normal.Symmetric m where
  cov x y := ↑(B x y)
  symm x y := congr_arg _ (congr_fun (congr_fun h y) x)

-- real scalar tensor lift utilities (in native *counting* units)
section units
variable {r s t : ℕ} {o : Side} (G)
lemma promote_prod (B : Matrix (Body r n) (Body s f) ℝ) (A : Matrix (Body s f) (Body t c) ℝ) :
    tensor G (B*A) = tensor G B * tensor G A := by
  ext ⟨x,b,i⟩ ⟨y,a,j⟩
  simp only [tensor,Matrix.of_apply,Matrix.mul_apply]
  simp_rw [Fintype.sum_prod_type]
  by_cases h : i=j <;> simp [h,ite_mul]
lemma promote_sum (B A : Matrix (Body r n) (Body s f) ℝ) : tensor G (B+A)=tensor G B+tensor G A := by ext i j; by_cases h : i.2.2=j.2.2 <;> simp [tensor,h]
lemma promote_diff (B A : Matrix (Body r n) (Body s f) ℝ) : tensor G (B-A)=tensor G B-tensor G A := by ext i j; by_cases h : i.2.2=j.2.2 <;> simp [tensor,h]
lemma promote_coeff (x : ℝ) (B : Matrix (Body r n) (Body s f) ℝ) : tensor G (x • B)=x • tensor G B := by ext i j; by_cases h : i.2.2=j.2.2 <;> simp [tensor,h]
lemma promote_zero (n f : Side) (r s : ℕ) : tensor G (0: Matrix (Body r n) (Body s f) ℝ)=0 := by ext i j; simp [tensor]
lemma promote_one (n : Side) (r : ℕ) : tensor G (1: Matrix (Body r n) (Body r n) ℝ)=1 := by ext ⟨x,b,i⟩ ⟨y,a,j⟩; by_cases h : i=j <;> simp [tensor,h, Matrix.one_apply]
end units

section free
variable (A : Levels G) (N i p : ℕ)

-- E normalization no physical `a_j` powers here. Native Y variables already
-- in coefficient units normalized by anneals/current `g`. Real PAC counting.
def complete : Matrix (Slot G (A.S.side i p) 2) (Slot G (A.S.side i p) 2) ℝ :=
  tensor G (scalarCov A.clock.kernel.penalty (location A N i) (A.S.side i p))

/-- Uncolored ψ (E psidif). Uses the whole cross row, so `installed` adds
all images on the period, not a shortest wrapped path. -/
def psiStep := installed (A.clock.op i p).ratio ((destination A N i).psi A.clock.kernel.penalty)

def passage := tensor G (psiStep A N i p)

lemma symmetric_complete : (complete A N i p)ᵀ=complete A N i p := by
  rw [complete,tensor_transpose,scalar_symm A.clock.kernel.penalty_pos]
lemma complete_closed : tensor G (Exterior.d 2 (A.S.side i p))*complete A N i p = 0 := by
  rw [complete, ← promote_prod, scalar_closed A.clock.kernel.penalty_pos, promote_zero]

def kappa := toNormal ((complete A N i p).submatrix toPAC toPAC) (by
    rw [Matrix.transpose_submatrix,symmetric_complete])

variable {i} in
lemma cov_at (x y : Chamber G A.S i p) :
    (kappa A N i p).cov x y = if x.2.2=y.2.2 then
      Episode.found A.clock.kernel.penalty (location A N i) (A.S.side i p) (plaquette x.2.1) (plaquette y.2.1) (lift x.1-lift y.1) else 0 := by
  change (↑(if x.2.2=y.2.2 then scalarCov A.clock.kernel.penalty (location A N i) _ (x.1,plaquette x.2.1) (y.1,plaquette y.2.1) else (0:ℝ)) : ℂ)=_
  split
  · exact scalar_entry A.clock.kernel.penalty_pos _ _ _
  rfl

-- Full real values summed periodically, then Finsupp just to enter the
-- finite torus composition in Rank. No fine Mote/cut predicates assumed.
def pathRow (x : Incidence G (A.S.side (i+1) p)) : Incidence G (A.S.side i p) →₀ ℂ :=
  Finsupp.equivFunOnFinite.symm fun y=> (↑(passage A N i p (toPAC x) (toPAC y)):ℂ)

def stamp : AtlasData G A.S p := ⟨fun i=> kappa A N i p,fun i=> pathRow A N i p⟩

lemma path_entry (x : Chamber G A.S (i+1) p) (y : Chamber G A.S i p) :
    (stamp A N p).path i x y = ↑(passage A N i p (toPAC x) (toPAC y)) := by
  change pathRow A N i p x y = _; unfold pathRow; simp

lemma stamp_pairs (x y : Chamber G A.S i p) :
    ((stamp A N p).κ i).cov x y = ↑(complete A N i p (toPAC x) (toPAC y)) := rfl

lemma lift_lag (x y : Cover) (u v : Beamer.Address G) :
    ((stamp A N p).κ i).cov (body x u) (body y v)= if u.2.2=v.2.2 then Episode.found A.clock.kernel.penalty (location A N i)
      (A.S.side i p) (plaquette u.2.1) (plaquette v.2.1) (x+u.1-(y+v.1)) else 0 := by
  rw [stamp]
  change (kappa A N i p).cov _ _=_
  rw [cov_at]
  unfold body; dsimp only; split
  · apply Episode.wraps; rw [map_sub,wrap_lift,wrap_lift,map_sub]
  rfl

-- Shows this exact stencil also has the imported Kper cost, NOT asserting
-- that this estimate handles the x=0 lift; includes large x lifting
-- to the same site but of course keeps the finite-period error there.
-- Basis entries at different colors are zero (see lift_lag).


lemma control_same (B : ℕ) (w : Cover) : Atlas.control (k:=i) (stamp A N p) w B=Atlas.control (k:=i) (stamp A N p) 0 B := by
  apply Normal.Symmetric.ext; funext x y; unfold Atlas.control
  simp_rw [Normal.match_name]
  rw [lift_lag,lift_lag]
  split_ifs; simp
  rfl

lemma stamp_real (x y) : (↑(((stamp A N p).κ i).cov x y).re : ℂ)=((stamp A N p).κ i).cov x y := by rw [stamp_pairs]; simp
lemma path_real (x y) : (↑((stamp A N p).path i x y).re : ℂ)=(stamp A N p).path i x y := by rw [path_entry]; simp

/-- One actual physical period vs k units, needed also for the derivative
ratio below. -/
lemma distances : A.S.a i/A.S.a (i+1) = ((A.S.block i).val : ℝ) ∧
    ((A.S.side i p).val:ℝ)*A.S.a i = (A.S.period p).val := by
  have he := A.S.embeds_scale (A.S.oneStep i p)
  constructor
  · rw [div_eq_iff (A.S.a_pos _).ne']; rw [mul_comm]; exact he.symm
  rw [mul_comm]; exact A.S.span_side i p

/-- Require the real unmasked history ties for uses with Bed. Allow
modified root / inverse metric as selected at these N, even with a
*different* modifier at the cutoff (cf boundaryPresent). `Suffices`
with its actual positive prices still needed, not allocated from this
identity port by measuring the family. -/
def ShapePort (A : Levels G) (H : Horizon A) (l : ℕ → ℕ → ℝ) :=
    (∀ N i,i ≤ N → Defined A.clock.kernel.penalty (l N i) (location A N i) (H.H N i)) ∧
    (∀ N i,i < N → (H.towers N i).A0=((destination A N i).duo A.clock.kernel.penalty).A0 ∧
      (H.towers N i).T=((destination A N i).duo A.clock.kernel.penalty).T)



/-- Identify ψ without changing M/T choices across p. -/
lemma psi_physical {l : ℕ → ℕ → ℝ} (H : Horizon A) (h : ShapePort A H l) (hi : i < N) :
    psiStep A N i p = (H.H N (i+1)).dual_diag.acts (A.S.side (i+1) p) * installed (A.clock.op i p).ratio (H.towers N i).T * (H.H N i).diagonal.acts (A.S.side i p) := by
  let W := destination A N i
  rw [(h.1 N _ hi).dual,(h.1 N i hi.le).diag,loc_land A N i hi,(h.2 N i hi).2]
  exact W.psi_bridge A.clock.kernel.penalty A.clock.kernel.penalty_pos (A.clock.adm i) (A.S.oneStep i p).exact_size

-- Alias receipt: complete finite Runs identity. `readings` uses **every**
-- (coarse p, alias) including harmonic and even-side tie, not only a
-- principal alias box. L^-2 symbol scaling in fromBank distinct from
-- ratio L^4 in counting adjoint.


-- Also identify literally with the current finite comparison receipt in
-- CORRECTED_LIFT (Copper). It establishes the curl inverse even with singular
-- harmonic in potential variables. These history ports will be explicit.
lemma copper_stamp {K : MapPrices} {l} (H : Horizon A) (h : ShapePort A H l) (hg : H.Suffices K) (hi : i≤N) (x y : Chamber G A.S i p) :
    ((stamp A N p).κ i).cov x y = (↑((Further.CorrectedLift.FacePrice.funds G (hg.all _ _ hi (A.S.side i p)) (K.eta_pos _)).P ((x.1,x.2.1),x.2.2) ((y.1,y.2.1),y.2.2)) : ℂ) := by
  rw [stamp_pairs,complete,scalar_eq_screen (hg.all _ _ hi (A.S.side i p)) (K.eta_pos _)
    (h.1 _ _ hi) (A.clock.adm i) A.clock.kernel.penalty_pos]; rfl
open Further.CorrectedLift in
/-- Spin test on these actual positive coordinates using the same `ShapePort`.
The base points in this formula can shift (negative axes after rotation). -/
lemma signed_cash {K : MapPrices} {l} (H : Horizon A) (h : ShapePort A H l) (hg : H.Suffices K)
    (hi : i≤N) (s : Signed) (x y : Chamber G A.S i p) :
    let q : Incidence G (A.S.side i p) → Incidence G (A.S.side i p) := fun z =>
      let w:=Face.send s (0:Site (A.S.side i p)) (z.1,z.2.1)
      (w.1,w.2,z.2.2)
    let c := ((stamp A N p).κ i).cov
    (↑(Compass.wind s x.2.1 * Compass.wind s y.2.1) : ℂ) * c (q x) (q y)=c x y := by
  intro q c; unfold c
  rw [copper_stamp A N i p H h hg hi,copper_stamp A N i p H h hg hi,← Complex.ofReal_mul]
  congr 1
  exact FacePrice.shadows _ _ G s A.clock.kernel.penalty_pos (A.clock.adm i) _ _ (h.1 N i hi) ((x.1,x.2.1),x.2.2) ((y.1,y.2.1),y.2.2)
end free
end YM.PhysicalNext.RankCovariance
