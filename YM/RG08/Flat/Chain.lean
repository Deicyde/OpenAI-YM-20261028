import YM.RG08.Flat.KStep

/-!
# Precise flat Wilson history used for the formal coefficients

Adapter from the *same* actual gauge history; no existential tuning/volume
limits used here. Also admits contexts with no deep-demand promises (fixed
smoothing formal tests). `pair` extends to artificial periods with exactly
the same cover-block germ. Does not supply real Estimates for those periods.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Filter Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08
open scoped Topology BigOperators

structure Chain where
  S : Schedule
  kernel : KernelChoices
  J : ℕ→ℕ
  adm i : 4 ≤ J i
  mono i : J i ≤ J (i+1)
  slow i : J (i+1) ≤ J i + 1

namespace Chain
variable (X : Chain) {G : Gauge}

/-- Blocking can be imported *literally* from the cutoff witness. -/
def actual (a : Levels G) : Chain := ⟨a.S,a.clock.kernel,a.clock.J,a.clock.adm,
    fun _ => a.fits.mono (Nat.le_succ _),a.fits.stepSlow⟩

def patch (m : ℕ) : Patch :=
    ⟨X.S.block m,X.J (m+1),X.adm _,X.S.block_large m,X.S.block_odd m⟩

def pair (m : ℕ) (c f : Side) (h : f.val=c.val*(X.S.block m).val) : StepData c f :=
    ⟨X.patch m,X.kernel,h⟩
def stepOp (m p : ℕ) : StepData (X.S.side m p) (X.S.side (m+1) p) :=
    X.pair m _ _ (X.S.oneStep m p).exact_size
lemma stepOp_uses (a : Levels G) (m p) : (actual a).stepOp m p = a.clock.op m p := rfl

def step (m : ℕ) (v : Train (X.J (m+1))) : Flight (X.J (m+1)) (X.J m) :=
    ⟨X.S.block m,X.S.block_odd _,X.S.block_large _,X.adm _,X.mono m,X.slow m,v⟩
def link (d i : ℕ) : Train (X.J i) := match d with
    | 0 => Train.top _
    | d+1 => (X.step i (link d (i+1))).land
def history (N i : ℕ) := X.link (N-i) i
lemma history_top (N : ℕ) : X.history N N=Train.top _ := by rw [history,Nat.sub_self,link]
def flight (N i : ℕ) := X.step i (X.history N (i+1))
lemma history_step (N i : ℕ) (h : i<N) : X.history N i=(X.flight N i).land := by
  unfold flight history; rw [show N-i = N-(i+1)+1 by omega, link]

def metric (N m : ℕ) := pink X.kernel.penalty (X.history N m)
/-- fluctuation order zero unscaled Hessian, *not* a physical derivative. -/
def K₀ (N i : ℕ) : KRow := hessian (X.metric N i)

def A₀ (N m : ℕ) : Cross (X.S.block m) (TypeFace 1) (TypeFace 1) :=
    ((X.flight N m).duo X.kernel.penalty).A0

lemma metric_whole (N m) : Whole (X.metric N m) :=
    (heart_saves X.kernel.penalty X.kernel.penalty_pos (X.adm _) (id : Train (X.J m) → _)).1.whole (X.history N m)
lemma k_whole (N m) : Whole (X.K₀ N m) := hessian_whole (X.metric_whole ..)
lemma metric_start (N m) : (X.metric N m).read 0=1 :=
    ((heart_true _ X.kernel.penalty_pos (X.adm _) (X.history N m)).1.echo 0
      ⟨(by unfold physical; simp),by intro i; simp [Real.pi_pos.le]⟩).trans (pulse_zero ..)
lemma metric_sym (N m) (c : Side) : ((X.metric N m).acts c)ᵀ=(X.metric N m).acts c :=
    (heart_inverse X.kernel.penalty X.kernel.penalty_pos (X.adm _) (X.history N m) c).2.1
lemma metric_wilson (N : ℕ) : X.metric N N=unitRow _ := by
  apply bank_injective (X.metric_whole ..).safe (Whole.coin _).safe
  apply Whole.eq_on (X.metric_whole ..) (Whole.coin _)
  intro p hp
  unfold metric pink; rw [X.history_top]
  apply Eq.trans ((heart_true X.kernel.penalty X.kernel.penalty_pos (X.adm _) (Train.top (X.J N))).1.echo _ hp)
  exact (top_metric _ X.kernel.penalty_pos _ (base_subset_realCube zone_pos hp)).2.trans (read_unit ..).symm

lemma sym_acts (N m) (c : Side) : (X.K₀ N m).acts c= K ((X.metric N m).acts c) :=
    hessian_acts (X.metric_whole ..) c
lemma canonical (N m) (hn:m<N) {c f : Side} (h : f.val=c.val*(X.S.block m).val) :
    Inputs (X.pair m c f h) (installed (X.pair m c f h).ratio (X.A₀ N m))
      ((X.metric N (m+1)).acts f) ((X.metric N m).acts c) := by
  unfold metric; rw [X.history_step N m hn]
  exact ((X.flight N m).tangent X.kernel (X.adm _) (c:=c) (f:=f) h).1
lemma az_whole (N m) : Whole (X.A₀ N m) := by
  obtain ⟨t,C,ht,-,H⟩ := ((secure_both _ X.kernel.penalty_pos (X.adm (m+1)) (X.adm m)).1).honored (X.adm (m+1)) 1
  exact ⟨_,_,ht,H (X.flight N m) [] (Nat.zero_le _)⟩

lemma link_actual (a : Levels G) (m n) : (actual a).link m n = flying a m n := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih => rw [link,ih, flying]; rfl
lemma A₀_actual (a : Levels G) (N m) : (actual a).A₀ N m=((destination a N m).duo a.clock.kernel.penalty).A0 := by
  unfold A₀ flight history; rw [link_actual]; rfl
lemma metric_actual (a : Levels G) (N m) : (actual a).metric N m=pink a.clock.kernel.penalty (location a N m) := by
  unfold metric history; rw [link_actual]; rfl

lemma side_infinite (s : YM.Schedule) (m : ℕ) : Tendsto (fun i => (s.side m i).val) atTop atTop := by
  refine tendsto_atTop_mono (fun i => ?_) s.period_strict.tendsto_atTop
  exact Nat.le_mul_of_pos_right _ (s.denominator m).property

/-- No A-A' difference on the right. -/
theorem k_difference_step (m N N' : ℕ) (h:m<N) (hh:m<N') :
    minusRows (X.K₀ N m) (X.K₀ N' m) =
      pullbackRows (X.A₀ N m) (X.A₀ N' m) (minusRows (X.K₀ N (m+1)) (X.K₀ N' (m+1))) :=
  cross_pullback (X.S.side m) (X.S.side (m+1)) (X.stepOp m) (X.S.block m) (fun _ => rfl)
    (side_infinite X.S m) (X.metric_whole _ _) (X.metric_whole _ _) (X.metric_whole _ _) (X.metric_whole _ _)
    (X.az_whole _ _) (X.az_whole _ _)
    (.of_forall fun i => ⟨X.canonical _ _ h (c:=X.S.side m i) (f:=X.S.side (m+1) i) (X.S.oneStep m i).exact_size,
      X.canonical _ _ hh (c:=X.S.side m i) (f:=X.S.side (m+1) i) (X.S.oneStep m i).exact_size,
      X.metric_sym .., X.metric_sym ..⟩)

/-- Any horizon with the actual Rack identities yields precisely this Hessian on
     every admitted level, not claiming similar uniqueness for higher real path data. -/
theorem same_rack (a : Levels G) (Q : Horizon a) (p : MapPrices) (h : Craft.Rack a p Q)
    (N m : ℕ) (hm:m≤N) : (actual a).K₀ N m=hessian (Q.H N m).metric := by
  let s := actual a
  have hv i hi : Whole (Q.H N i).metric :=
    ⟨_,_,p.alpha_pos _, (h.covers N i hi).2.1⟩
  have hk i L : (s.K₀ N i).acts L= K ((s.metric N i).acts L) := sym_acts ..
  change s.K₀ N m=_
  induction hm using Nat.decreasingInduction with
  | self =>
    apply bank_injective (s.k_whole ..).safe (hessian_whole (hv _ le_rfl)).safe
    intro L
    rw [hessian_acts (hv _ le_rfl),hk,s.metric_wilson,acts_unit]
    have hz := (h.traces N N le_rfl L).same
    rw [h.top] at hz
    rw [K,K,Matrix.mul_assoc, Matrix.mul_assoc, hz]
  | of_succ i hi IH =>
    apply row_ext_tail (side_infinite a.S i) (s.k_whole ..).safe (hessian_whole (hv _ hi.le)).safe
    refine Eventually.of_forall fun z => ?_
    let F := a.S.side (i+1) z; let c := a.S.side i z
    let S := a.clock.op i z
    have ha := s.canonical _ _ hi (c:=c) (f:=F) (a.S.oneStep i z).exact_size
    have hX := cross_identity S (s.metric_sym ..) (s.metric_sym ..) ha (h.crosses N i z hi|>.trial)
    have hm := hv (i+1) hi
    have hs : s.K₀ N (i+1) = _ := IH
    rw [← hk (i+1) F,hs,hessian_acts hm,sub_self,Matrix.mul_zero,Matrix.zero_mul] at hX
    rw [hk i c,hessian_acts (hv _ hi.le)]; exact sub_eq_zero.mp hX

end Chain
end YM.RG08
