import YM.WilsonBulk.Grid.PullCost
import YM.Work.F08

/-!
# Leading flat primitive and Ward normalization

Unmodified *potential-field* precision (not two-form metric). Slice changes at order zero are
along gradients and needn't be estimated at this point. Treat harmonic fibers as in the actual
Horizon API. This obtains a three-discrete-moment nullity for differences at two cuts even though
the cover size, pole split and lifted gauge rows can change. Costs in Laurent convention.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Lattice Laurent Filter Function Bloch
open Push.AbsoluteSums RG Finset Work.F08 Precision Exterior Craft
open scoped Topology BigOperators Classical
open Matrix

abbrev PotentialForm := TypeFace 1
abbrev Two := TypeFace 2
variable {P Q : Row Two Two} {σ A B H : ℝ}
-- NOTE map of kernel, not of paths. Reads every torus, not projected zero mode.
def actionKernel (P : Row Two Two) : Row PotentialForm PotentialForm :=
  composeRows (composeRows (transRows (cobound 1)) P) (cobound 1)
def kprice (σ A : ℝ) := (Fintype.card Two:ℝ) * ((Fintype.card Two * (stencilCost 1 σ * A)) * stencilCost 1 σ)
lemma actionKernel_strip (hs : 0≤σ) (h : P.strip σ A) : (actionKernel P).strip σ (kprice σ A) :=
  strip_compose hs (strip_compose hs (strip_trans (strip_stencil 1 σ)) h) (strip_stencil _ _)
lemma actionKernel_acts (hs : 0≤σ) (h : P.strip σ A) (n : Side) :
    (actionKernel P).acts n = K (P.acts n) := by
  unfold actionKernel; rw [acts_compose hs (strip_compose hs (strip_trans (strip_stencil 1 σ)) h) (strip_stencil 1 _),
    acts_compose hs (strip_trans (strip_stencil 1 σ)) h, acts_trans]; rfl
lemma actionKernel_diff (hs : 0≤σ) (h : P.strip σ A) (hp : Q.strip σ B) :
    actionKernel (minusRows P Q) = minusRows (actionKernel P) (actionKernel Q) := by
  apply Next.Free.bank_injective (Row.rights _ _ (actionKernel_strip hs (strip_minus h hp)) hs)
    (Row.rights _ _ (strip_minus (actionKernel_strip hs h) (actionKernel_strip hs hp)) hs)
    (fun n=>?_)
  rw [acts_minus hs (actionKernel_strip hs h) (actionKernel_strip hs hp), actionKernel_acts hs (strip_minus h hp),
    actionKernel_acts hs h, actionKernel_acts hs hp, acts_minus hs h hp]
  simp only [K,Matrix.mul_sub,Matrix.sub_mul]

lemma face_blind : (cobound 1).read 0 = 0 := by
  rw [reading]; simp [symbol, Exterior.q, wedge]
lemma normalized (hs : 0< σ) (h : P.strip σ A) (hk : Q.strip σ B) (hz : P.read 0=Q.read 0)
    (i j) : Blind 3 (minusRows (actionKernel P) (actionKernel Q) i j) := by
  rw [← actionKernel_diff hs.le h hk]
  have hT := strip_trans (strip_stencil 1 σ)
  have he := strip_minus h hk
  exact Blind.compose hs hs (strip_compose hs.le hT he) (strip_stencil _ _)
    (Blind.compose hs hs hT he (blind_trans_one (cobound 1) (cobound_safe 1) face_blind) (blind_minus hs.le hs.le h hk hz))
    (signal_one (cobound_safe _) face_blind) i j

-- use from actual Levels h; separate gauge kernel from independent metric choice
variable {G : Gauge} {a : Levels G} (H : Horizon a)
def flat (N m : ℕ) := actionKernel (H.H N m).metric
variable {H} {F : MapPrices} {N m : ℕ}

lemma canonical_strip (h : H.Suffices F) (hm : m ≤ N) :
    (flat H N m).strip (F.α (a.clock.J m)) (kprice (F.α (a.clock.J m)) (F.Ω (a.clock.J m))) :=
  actionKernel_strip (F.alpha_pos _).le (h.rows N m hm).2.1

lemma canonical_period (h : H.Suffices F) (hm : m ≤ N) (n : Side) :
    (flat H N m).acts n = K ((H.H N m).metric.acts n) :=
  actionKernel_acts (F.alpha_pos _).le (h.rows N m hm).2.1 n

lemma canonical_peak (h : H.Suffices F) (N : ℕ) (n : Side) :
    (flat H N N).acts n = (d 1 n).transpose * d 1 n := by
  rw [canonical_period h le_rfl, K, Matrix.mul_assoc, (h.all N N le_rfl n).same,h.top N n, Matrix.one_mul]

lemma ksym {f : Side} {R : Matrix (Body 2 f) (Body 2 f) ℝ} (h : R.transpose = R) :
    (K R).transpose = K R := by simp [K, h, Matrix.mul_assoc]

lemma blind_flat_diff {P : Horizon a} {F' : MapPrices} (h : H.Suffices F) (hP : P.Suffices F') {N' : ℕ}
    (hm : m ≤ N) (hm' : m ≤ N') (i j) : Blind 3 (minusRows (flat H N m) (flat P N' m) i j) :=
  normalized (lt_min (F.alpha_pos _) (F'.alpha_pos _))
    (strip_mono (h.rows N m hm).2.1 (min_le_left ..) le_rfl)
    (strip_mono (hP.rows N' m hm').2.1 (min_le_right ..) le_rfl)
    ((h.all N m hm 1).starts.trans (hP.all N' m hm' 1).starts.symm) i j

end YM.WilsonBulk
