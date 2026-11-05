import YM.Next.RANK.Odometer
import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Consumer
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Issue.Cut.Cells


/-!
# Short rows for V. Use the stamp actually bound to the plan

E (kcr) path model on this step. For Ψ keep full lifts and cut with a
radius at `clim i`. For the conditional covariance we use a NUMERICAL cut of the complete periodic
kernel, not the generally different computation on the cut displacement
stencil. Chosen for ease of comparison; still close at the after-L rate required by Rank
(proved from actual 45C cover costs in Epoch, before any W polynomial substitution).
Does not assert compatibility or H symmetry of *rotated* lifted row metadata.
Rank stencil asks for spatial support and GLOBAL Ad, not a realized law with
this short covariance.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch WeightedGaussianMarginal45C.Issue.Cut
    AnalyticBridge.LocalGaussianLaws Work.F08 FreeResolvent Exterior
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- Radius in the old geometry used for the F/rank estimates. -/
def takePaths (α β : Type*) (x : ℝ) : ShapeCut α β x :=
  { retain := fun _ _ j => Laurent.size j ≤ leastHem x
    copay := fun _ _ _ hj => hj
    spatial := fun _ _ _ hj => hj.trans (by unfold leastHem lastHem; omega) }
lemma path_flip (α : Type*) (x : ℝ) : swizzles (takePaths α α x) := by
  intro i j z; change Laurent.size z ≤ _ ↔ Laurent.size (-z) ≤ _; rw [size_neg]



section plan
variable {C : Family G} (B : Binding C) (N i p : ℕ)
local notation "S" => C.path.levels.clock.op i p
local notation "x" => C.path.levels.clock.hatBeta i

def curves := coverPsi (B.world.H N (i+1)) (B.world.H N i) (B.world.towers N i)
def shorter := (takePaths _ _ x).draw (curves B N i)
def Hrow (u : Incidence G (C.side (i+1) p)) : Incidence G (C.side i p) →₀ ℂ := Finsupp.equivFunOnFinite.symm
    fun v => (panePsi G S (shorter B N i) (toPAC u) (toPAC v) : ℂ)

def Qrow : Normal.Symmetric (Incidence G (C.side (i+1) p)) :=
    let V := (track (stamp C.path.levels N p) i).Q
    { cov := fun u v => if separation ((C.path.levels.clock.op i p).ratio.parent u.1) ((C.path.levels.clock.op i p).ratio.parent v.1) ≤ lastHem x then V.cov u v else 0
      symm := fun u v => by rw [separation_comm,V.symm u v] }

def short : Lead G C.S p := fun i => ⟨Hrow B N i p, Qrow (C:=C) N i p⟩

variable (hh : i<N)

lemma H_at u v : (short B N p i).H u v=(panePsi G S (shorter B N i) (toPAC u) (toPAC v):ℂ) := by
  change Hrow B N i p u v = _
  simp [Hrow]

include hh
lemma planner_at u v : (track (stamp C.path.levels N p) i).H u v =
      (tensor G (Current.psi S (B.world.H N (i+1)) (B.world.H N i) (B.world.towers N i)) (toPAC u) (toPAC v):ℂ) := by
  change (stamp C.path.levels N p).path i u v=_
  rw [path_entry,passage,psi_physical C.path.levels N i p B.world B.present hh]; rfl

lemma gaussian_stamp (F : Tree.Forest (C.path.levels.clock.op i p).ratio) :
    let f:= C.side (i+1) p; let H:=B.world.H N (i+1); let P:=B.world.H N i; let R:=B.world.towers N i
    latticeCurl G f * flat B.world N i p F * (latticeCurl G f).transpose=tensor G (Current.fConditional S H P R) := by
  intro f H P R
  have hx := Current.cutHead S F H (B.sized i p) (B.pays.all N (i+1) hh f) (B.prices.eta_pos _) R
    (B.pays.all N i hh.le (C.side i p)) (B.prices.eta_pos _) (B.pays.crossings N i p hh)
  unfold latticeCurl flat FreeResolvent.covariance Current.plane at *
  simp only [FreeResolvent.reduce,Matrix.transpose_mul,Matrix.mul_assoc] at hx ⊢; exact hx

lemma planner_Q u v : (track (stamp C.path.levels N p) i).Q.cov u v =
      (tensor G (Current.fConditional S (B.world.H N (i+1)) (B.world.H N i) (B.world.towers N i)) (toPAC u) (toPAC v):ℂ) := by
  let F := Classical.choice (Tree.select (C.path.levels.clock.op i p).ratio (C.path.levels.clock.op i p).patch.odd_side)
  rw [← principal_match B.present B.pays hh F (B.sized i p),tag_entries B.pays hh F u v,show latticeCurl G _ * flat B.world N i p F * (latticeCurl G _).transpose= _ from gaussian_stamp B N i p hh F]
end plan

section finances
open Next.Free Flux Filter
private lemma row_sum_full (A : veilPsi S.patch.L) {s M : ℝ} (hs : 0<s) (hp : A.strip s M)
    (i : FreeResolvent.Slot G f 2) :
    ∑ j, |panePsi G S A i j| ≤ ticket (TypeFace 2) M := by
  let z := (i.1,i.2.1); let e := splitCo S.ratio (TypeFace 2)
  have hh := row_sprawl (show 0≤(0:ℝ) from le_rfl) (strip_mono hp hs.le le_rfl) c (e z)
  simp only [zero_mul,Real.exp_zero,one_mul] at hh
  have H : (∑ j, |panePsi G S A i j|) = ∑ j:Body 2 c, |A.acts c (e z) j| := by
    unfold panePsi; simp only [tensor, Matrix.of_apply,Fintype.sum_prod_type,apply_ite abs,abs_zero]; simp; rfl
  rw [H]; exact hh

variable {C : Family G} (B : Binding C) {N i p : ℕ}

-- Use rows on B. These hypotheses (per step) available from Binding and
-- levels on same C. Use also later with V PATH still equal.
local notation "s" => C.path.levels.clock.op i p
local notation "x" => C.path.levels.clock.hatBeta i
local notation "X" => stamp C.path.levels N p
variable (h : i < N)

lemma paths_contained {t C' : ℝ} (ht : 0<t) (hp : (curves B N i).strip t C') (u v) :
    lastHem x < separation ((C.path.levels.clock.op i p).ratio.parent u.1) v.1 →
      (short B N p i).H u v=0 := by
  intro hh
  rw [H_at]
  have H := contour_uses (S:=s) (curves B N i) ht hp (takePaths _ _ x) (toPAC u)
  rw [show panePsi G s (shorter B N i) (toPAC u) (toPAC v)=0 from H.2.2 (toPAC v) hh]; rfl


lemma support_rows {t C' : ℝ} (ht : 0<t) (hp : (curves B N i).strip t C') :
    Tapes.Mote (A:=C.path.levels) (short B N p) i := by
  let b := M (Atlas.clim C.path.levels i); let B':= lastHem x
  have hb : B' ≤ walls x := by
    have ht : 0<b:=(C.path.levels.budget i).B_pos
    have he : B'≤b := Nat.div_le_self _ _
    change B' ≤ b^2; rw [pow_two]
    exact he.trans (Nat.le_mul_of_pos_left _ ht)
  constructor
  · intro u v hz; contrapose! hz
    change (Qrow N i p (C:=C)).cov u v=0
    exact if_neg (not_le.mpr (lt_of_le_of_lt hb hz))
  intro u v hz; contrapose! hz
  exact Finsupp.notMem_support_iff.mpr (paths_contained B ht hp u v (lt_of_le_of_lt hb hz))

lemma exact_short_price {t C' : ℝ} (ht : 0<t) (hp : (curves B N i).strip t C') (u : Incidence G (C.side (i+1) p)) :
    ∑ v, ‖(short B N p i).H u v‖ ≤ ticket (TypeFace 2) C' := by
  simp_rw [H_at, Complex.norm_real, Real.norm_eq_abs]
  let W : FreeResolvent.Slot G (C.side i p) 2 → ℝ := fun j => |panePsi G s (shorter B N i) (toPAC u) j|
  apply ((Equiv.sum_comp toPAC W).trans_le ·)
  exact row_sum_full _ ht (cut_bounds hp ht.le (takePaths _ _ x)).1 _

include h
variable (hh : C.path.levels.clock.J (i+1)=C.path.levels.clock.J i)
local notation "J" => C.path.levels.clock.J i
local notation "z" => B.prices.Ω J
local notation "t" => B.prices.α J

include hh
lemma sufficient_rows : (curves B N i).strip t (psiBudget z / ((C.S.block i).val:ℝ)^2) := by
  -- apply Deep, not estimating new Pt overhead from post-L x
  let D := B.world.towers N i
  let A := B.world.H N (i+1); let H:=B.world.H N i
  have hf : A.dual_diag.strip t z := hh ▸ (B.pays.rows N (i+1) h).2.2.2.2
  have he : H.diagonal.strip t z := (B.pays.rows N i h.le).1
  let k := ((C.S.block i).val:ℝ)^2
  have ha : D.T.strip t (z/k) := hh ▸ ((B.pays.costs N i h).2.2.2 [] (Nat.zero_le _)).2
  have hr := (B.prices.alpha_pos J).le
  have H' := strip_compose hr (strip_fine hr hf ha) he
  convert H' using 1
  · rfl
  dsimp only [psiBudget]; unfold k; ring

lemma rich_path u v : (track X i).H u v = (panePsi G s (curves B N i) (toPAC u) (toPAC v) : ℂ) := by
  rw [planner_at B _ _ _ h]
  let D := B.world.towers N i; let A':= B.world.H N (i+1); let B':= B.world.H N i
  have hf : A'.dual_diag.strip t z := hh ▸ (B.pays.rows N (i+1) h).2.2.2.2
  have he : B'.diagonal.strip t z := (B.pays.rows N i h.le).1
  let k := ((C.S.block i).val:ℝ)^2
  have ha : D.T.strip t (z/k) := hh ▸ ((B.pays.costs N i h).2.2.2 [] (Nat.zero_le _)).2
  have hr := (B.prices.alpha_pos J).le
  have hy := strip_fine hr hf ha
  have ht : tensor G (Current.psi s A' B' D)=panePsi G s (coverPsi A' B' D) := by
    apply congr_arg
    unfold coverPsi Extra.Iteration.psi Extra.Iteration.moving; simp only [Option.elim]
    symm; erw [installed_compose (C.path.levels.clock.op i p).ratio hr hy he, installed_fine _ hr hf ha]; rfl
  rw [show panePsi G s (curves B N i) = _ from ht.symm]

lemma high_rows (u) : let P := psiBudget z / ((C.S.block i).val:ℝ)^2
    (∑ v, ‖(track X i).H u v‖) ≤ ticket (TypeFace 2) P ∧
    (∑ v, ‖(short B N p i).H u v - (track X i).H u v‖) ≤ cheque (TypeFace 2) t P x := by
  intro P
  have hr := B.prices.alpha_pos J
  simp_rw [H_at, rich_path B h hh,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  constructor
  · let W : FreeResolvent.Slot G (C.side i p) 2 → ℝ := fun j => |panePsi G s (curves B N i) (toPAC u) j|
    apply ((Equiv.sum_comp toPAC W).trans_le ·)
    exact row_sum_full _ hr (sufficient_rows B h hh) _
  have hf := (contour_uses (S:=s) (curves B N i) hr (sufficient_rows B h hh) (takePaths _ _ x) (toPAC u)).2.1
  let W : FreeResolvent.Slot G (C.side i p) 2 → ℝ := fun j=>|panePsi G s (shorter B N i) (toPAC u) j - panePsi G s (curves B N i) (toPAC u) j|
  apply ((Equiv.sum_comp toPAC W).trans_le ·)
  rw [show ∑ j, W j = _ from (show (∑ j, W j) = ∑ j, |panePsi G s (curves B N i) (toPAC u) j-panePsi G s (shorter B N i) (toPAC u) j| from
    Finset.sum_congr rfl (fun i _ => abs_sub_comm ..))]
  exact hf
end finances
end YM.PhysicalNext.InteractingRank
