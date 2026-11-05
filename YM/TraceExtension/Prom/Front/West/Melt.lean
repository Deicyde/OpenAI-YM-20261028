import YM.MergeProof.West.Melt
import YM.TraceExtension.Prom.Front.West.Mural
import YM.TraceExtension.Prom.Front.West.View
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Camps
import YM.TraceExtension.Prom.Hill.Joints
import YM.TraceExtension.Prom.Hill.Station
/-!
  Variant of YM.MergeProof.West.Melt for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Set MeasureTheory Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {V : Type*}
variable {C : Family G} {i k l j m p q d D a n N : ℕ}
variable {R : Lead G C.S p}
variable {hN : k≤N} {b : ℝ} {x : Points n} {hk : i<k} {h : middleSky C.path.levels b k ≤ i}
variable {c : Course C N p k}

lemma i_nsuredSky {k p i d B} (X : roomTestSky C.path.levels b k p d q) (h : middleSky C.path.levels b k≤ i) (H : i≤k) {W : Manner n} (Y : CellPSky C k b p)
    (f : Chamber G C.S i p) (U : Config G (C.side i p)) {c : Course C N p k}
    (hx : separation (core C.path.levels x b p H (Head W)) f.1 ≤ (d+8)*walls (clim C.path.levels i))
    (hQ : Healthy B (d_olmSky x b q (walls (clim C.path.levels i)) c.allow H Y W) U):
    ‖basisFtSky c x b i c.allow H h Y W U (fromBead G f)‖ ≤ B/anneals C c i:= by
  let A:=C.path.levels; let o:= core A x b p H (Head W); let w:=walls (clim A i); let T:=Ship.yardSky C b c.allow p
  let V:=watchesSky C b p c.allow i h Y U
  have ht: Healthy B (Spindle.patch (q*w) o) V:= by rw [seenPSky x b p c.allow H h Y] at hQ; exact (s_healthy (T.omega Y) ..).2 hQ
  have hp: spotFt (C:=C) b i d H x W f:= hx
  exact dotSize _ (warmth _ _ (H.trans c.allow)) V ht (X.suite i h H) (n_earbySky x b H W f hp X)
lemma turn_ftSky {p b B i k W} {U : Config G (C.side i p)} {c : Course C N p k} (X : roomTestSky C.path.levels b k p d q) (h : middleSky C.path.levels b k ≤ i) (H : i≤k) (Y : CellPSky C k b p) (f : Chamber G C.S i p) (hx : spotFt b i d H (C:=C) x W f)
    (hQ : Healthy B (d_olmSky x b q (walls (clim C.path.levels i)) c.allow H Y W) U) z:
    |rigid (coloring z (basisFtSky c x b i c.allow H h Y W U)) f| ≤ B/anneals C c i:= by
  refine (rigidHelm ..).trans ?_; unfold coloring; rw [G.norm_adjoint]; exact i_nsuredSky X h H Y f U hx hQ

lemma headFtSky (h : roomTestSky C.path.levels b k p d q) (X : BaleSky C k b p d x (show i ≤ k from hk.le))
    (a : PatchPt x b C.path.levels p d (show i+1≤k from hk)) (hp : t_ests (C:=C) x b hk X.2.val a) {u : Chamber G C.S (i+1) p} (hf : spotFt b (i+1) d hk x a.val u (C:=C))
    (hq : middleSky C.path.levels b k ≤ i) : let A:= C.path.levels; let P:= (A.clock.op i p).ratio;
                             separation (core C.path.levels x b p hk.le (Head X.2.val)) (P.parent u.1) ≤ (d+1)*walls (clim C.path.levels i):= by
  intro A P; have he:=p_rized (B:=hk.le) (C:=C) X.2 (Head a.val) (hp (head_member a.val))
  let t:=walls (clim A (i+1))
  have hh:d+8≤q:= by have hx:= h.radius; omega
  have hz:separation (core A x b p (show i+1≤k from hk) (Head a.val)) u.1≤ q*t:=le_trans hf (Nat.mul_le_mul_right _ hh)
  have hv := spends_aloftSky _ h hk hq _ _ hz; have ht:=itinerary A x b p hk (Head a.val)
  apply (separation_triangle _ (core A x b p hk.le (Head a.val)) _).trans; apply (add_le_add he (show separation (core A x b p hk.le (Head a.val)) (P.parent u.1) ≤ walls (clim A i) from ?_)).trans;swap
  · rw [ht]; exact hv
  rw [add_mul,one_mul]

-- cost at q from $s+1$ exponent

variable (T : BaleSky C k b p d x hk.le)
lemma predFtSky (hX : roomTestSky C.path.levels b k p d q) (h : middleSky C.path.levels b k ≤ i) {ε u v o M L} (t : Metal b c R hk ε u v o M L)
    (z : Config G (C.side i p)) (hU : Healthy v (d_olmSky x b q (walls (clim C.path.levels i)) c.allow hk.le T.1 T.2.val) z) j (hj : j∈ sp_okes x b hk d T.2.val (C:=C)) :
    ‖colorFtSky R c b x hk h T.1 T.2.val z j‖ ≤ o := by
  obtain ⟨y,hy,hr⟩:= (Finset.mem_filter.mp hj).2
  let A:= C.path.levels; let W:=(R i).H j; let ξ:= core A x b p hk.le; let m:= rigid (basisFtSky c x b i c.allow hk.le h T.1 T.2.val z); let V:= glyph W
  have hp : V.totalDegree≤1:= by simpa only [V,W, Normal.exchange_x,MvPolynomial.totalDegree_X] using ascent (R i).H (MvPolynomial.X j)
  have he : colorFtSky R c b x hk h T.1 T.2.val z j=text m V:= Eq.symm (by unfold text;rw [show V= Normal.exchange (R i).H (MvPolynomial.X j) from (exchange_x ..).symm, Normal.reads_val,aeval_X];rfl)
  rw [he]; apply le_trans (view_v _ _ hp t.stage ?_) (le_trans (mul_le_mul_of_nonneg_right (t.φ.charge j) (zero_le_one.trans (priced_up 1 t.stage))) t.sum)
  intro y' hi
  apply le_trans (rigidHelm _ _) (le_trans (i_nsuredSky (c:=c) hX h hk.le T.1 y' z ?_ hU) t.major)
  let k':= (A.clock.op i p).ratio
  apply (separation_triangle _ (k'.parent j.1) y'.1).trans
  apply (add_le_add (headFtSky hX T y hy hr h) (t.beaming.pole _ _ (glyph_vars W hi))).trans
  rw [add_mul,add_mul]; omega
end YM.Next.Rank.Tapes.West
