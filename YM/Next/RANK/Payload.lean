import YM.Next.RANK.CircleSense
import YM.Next.RANK.Currents

/-!
# Estimates on kiosk readings: inherited colors and mean

Apply on ANY actual mask of the statement. Path and covariance estimates here
need only on particular path (Ranging/F); explicitly real condition on means.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function Set MeasureTheory Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {V : Type*}
variable {C : Family G} {i k l j m p q d D a n N : ℕ}
variable {R : Lead G C.S p}
variable {hN : k≤N} {b : ℝ} {x : Points n} {hk : i<k} {h : middle C.path.levels b k ≤ i}
variable {c : Course C N p k}

lemma member_mark (x : pennant n) : headMark x∈ (tale x).val.val:= by
  cases x with
  | inl x=> exact Finset.mem_singleton_self _
  | inr x=> exact Finset.mem_insert_self ..
lemma prized {p b B} (T : Index x b C.path.levels p d (show j≤k from B)) (a) (ha : a∈(tale T.val).val.val):
    let A:= C.path.levels
    separation (core A x b p (show j≤k from B) (headMark T.val)) (core A x b p B a) ≤ d*walls (clim A j):= by
  intro A; cases T with
  | mk v H=>
    dsimp only at *; cases v with
    | inl α=> rw [show a=α from Finset.mem_singleton.mp ha]; exact (show _=0 from separation_self _).trans_le (Nat.zero_le _)
    | inr α=> rcases Finset.mem_insert.mp ha with ha|ha; rw [ha]; exact (show _=0 from separation_self _).trans_le (Nat.zero_le _)
              rw [show a=α.val.2 from Finset.mem_singleton.mp ha]; exact H
lemma insured {k p i d B} (X : roomTest C.path.levels b k p d q) (h : middle C.path.levels b k≤ i) (H : i≤k) {W : pennant n} (Y : CellP C k b p)
    (f : Chamber G C.S i p) (U : Config G (C.side i p)) {c : Course C N p k}
    (hx : separation (core C.path.levels x b p H (headMark W)) f.1 ≤ (d+8)*walls (clim C.path.levels i))
    (hQ : Healthy B (dolmens x b q (walls (clim C.path.levels i)) c.allow H Y W) U):
    ‖basisK c x b i c.allow H h Y W U (fromBead G f)‖ ≤ B/anneals C c i:= by
  let A:=C.path.levels; let o:= core A x b p H (headMark W); let w:=walls (clim A i); let T:=Ship.yard C b c.allow p
  let V:=watches C b p c.allow i h Y U
  have ht: Healthy B (Spindle.patch (q*w) o) V:= by rw [seenPatch x b p c.allow H h Y] at hQ; exact (s_healthy (T.omega Y) ..).2 hQ
  have hp: spotP (C:=C) b i d H x W f:= hx
  exact dotSize _ (warmth _ _ (H.trans c.allow)) V ht (X.suite i h H) (nearby x b H W f hp X)
lemma rigidHelm {o : Side} (V : Face (Per o) → G.Color) (u : bead G o) : |rigid V u| ≤ ‖V (fromBead G u)‖:= by
  let Q:=V (fromBead G u)
  rw [show rigid V u=inner ℝ ((EuclideanSpace.basisFun G.ColorIndex ℝ) u.2.2) Q from (EuclideanSpace.basisFun_inner ..).symm]; exact (abs_real_inner_le_norm ..).trans (by rw [OrthonormalBasis.norm_eq_one,one_mul])
lemma turn_strength {p b B i k W} {U : Config G (C.side i p)} {c : Course C N p k} (X : roomTest C.path.levels b k p d q) (h : middle C.path.levels b k ≤ i) (H : i≤k) (Y : CellP C k b p) (f : Chamber G C.S i p) (hx : spotP b i d H (C:=C) x W f)
    (hQ : Healthy B (dolmens x b q (walls (clim C.path.levels i)) c.allow H Y W) U) z:
    |rigid (coloring z (basisK c x b i c.allow H h Y W U)) f| ≤ B/anneals C c i:= by
  refine (rigidHelm ..).trans ?_; unfold coloring; rw [G.norm_adjoint]; exact insured X h H Y f U hx hQ

lemma headSpend (h : roomTest C.path.levels b k p d q) (X : Lane C k b p d x (show i ≤ k from hk.le))
    (a : Index x b C.path.levels p d (show i+1≤k from hk)) (hp : tests (C:=C) x b hk X.2.val a) {u : Chamber G C.S (i+1) p} (hf : spotP b (i+1) d hk x a.val u (C:=C))
    (hq : middle C.path.levels b k ≤ i) : let A:= C.path.levels; let P:= (A.clock.op i p).ratio;
                             separation (core C.path.levels x b p hk.le (headMark X.2.val)) (P.parent u.1) ≤ (d+1)*walls (clim C.path.levels i):= by
  intro A P; have he:=prized (B:=hk.le) (C:=C) X.2 (headMark a.val) (hp (member_mark a.val))
  let t:=walls (clim A (i+1))
  have hh:d+8≤q:= by have hx:= h.radius; omega
  have hz:separation (core A x b p (show i+1≤k from hk) (headMark a.val)) u.1≤ q*t:=le_trans hf (Nat.mul_le_mul_right _ hh)
  have hv := spends_aloft _ h hk hq _ _ hz; have ht:=itinerary A x b p hk (headMark a.val)
  apply (separation_triangle _ (core A x b p hk.le (headMark a.val)) _).trans; apply (add_le_add he (show separation (core A x b p hk.le (headMark a.val)) (P.parent u.1) ≤ walls (clim A i) from ?_)).trans;swap
  · rw [ht]; exact hv
  rw [add_mul,one_mul]

-- cost at q from $s+1$ exponent

structure Metal (s : ℝ) (g : Course C N p k) (R : Lead G C.S p) (hk : i<k) (ε τ T B M L : ℝ) : Prop where
  beaming : Mote (A:=C.path.levels) R i
  φ : (R i).Fair L
  grain : 1 ≤ B
  stage : 1 ≤ M
  fine : τ / anneals C g (i+1) ≤ B - 1
  major : T / anneals C g i ≤ M
  wake : L + ε ≤ B
  sum : L*Common.priced M 1 ≤ B
  path (m : Chamber G C.S i p → ℝ) i' :
    let z:= Normal.reads (R i).H (fun i=>(m i:ℂ)) i'
    z=(↑z.re:ℂ)

variable (T : Lane C k b p d x hk.le)
lemma predicts (hX : roomTest C.path.levels b k p d q) (h : middle C.path.levels b k ≤ i) {ε u v o M L} (t : Metal b c R hk ε u v o M L)
    (z : Config G (C.side i p)) (hU : Healthy v (dolmens x b q (walls (clim C.path.levels i)) c.allow hk.le T.1 T.2.val) z) j (hj : j∈ spokes x b hk d T.2.val (C:=C)) :
    ‖colorMean R c b x hk h T.1 T.2.val z j‖ ≤ o := by
  obtain ⟨y,hy,hr⟩:= (Finset.mem_filter.mp hj).2
  let A:= C.path.levels; let W:=(R i).H j; let ξ:= core A x b p hk.le; let m:= rigid (basisK c x b i c.allow hk.le h T.1 T.2.val z); let V:= glyph W
  have hp : V.totalDegree≤1:= by simpa only [V,W, Normal.exchange_x,MvPolynomial.totalDegree_X] using ascent (R i).H (MvPolynomial.X j)
  have he : colorMean R c b x hk h T.1 T.2.val z j=text m V:= Eq.symm (by unfold text;rw [show V= Normal.exchange (R i).H (MvPolynomial.X j) from (exchange_x ..).symm, Normal.reads_val,aeval_X];rfl)
  rw [he]; apply le_trans (view_v _ _ hp t.stage ?_) (le_trans (mul_le_mul_of_nonneg_right (t.φ.charge j) (zero_le_one.trans (priced_up 1 t.stage))) t.sum)
  intro y' hi
  apply le_trans (rigidHelm _ _) (le_trans (insured (c:=c) hX h hk.le T.1 y' z ?_ hU) t.major)
  let k':= (A.clock.op i p).ratio
  apply (separation_triangle _ (k'.parent j.1) y'.1).trans
  apply (add_le_add (headSpend hX T y hy hr h) (t.beaming.pole _ _ (glyph_vars W hi))).trans
  rw [add_mul,add_mul]; omega
end YM.Next.Rank.Tapes
