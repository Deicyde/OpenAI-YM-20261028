import YM.Extra.SOURCE_HISTORIES.Charts
import YM.Extra.SOURCE_HISTORIES.Play
import YM.Extra.SOURCE_HISTORIES.Tickets


/-!
# Literal aligned ancestors: same History, actual shifted addresses,
actual neighborhood decisions. Can follow from N to m when shifts
match the block embedding along *these* steps. There is no license here
to price many simultaneous markers, or use unchanged history coordinates
once offset no longer aligns. Off this chain the `O` above always still
uses literal translate, not independent retune.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories.Tour
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Bid Motion Drift
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge}

/-- Strict positivity for realized histories (used only to infer
translation identity for exp(exponent)). Even a finite-volume lower
bound on noise all configurations. Strengthens the pointwise positive
kernel observation in foundations to *any* purchased BlockControl, but
not uniform over physical parameters. -/
lemma bright_kernel {c f : Side} (S : StepData c f) (β : ℝ) (h : S.patch.Branches S.kernel G) :
    ∃ D : ℝ, 0<D ∧ ∀ U : Config G f, ∀ V, D ≤ S.density β U V := by
  let q (x : Config G c × Config G c) := S.noise β x.1 x.2
  obtain ⟨u,-,hu⟩ := isCompact_univ.exists_isMinOn (s:=univ) (f:=q) univ_nonempty (S.noise_cont β).continuousOn
  have hx (x) : 0<q x := Finset.prod_pos (fun i _ => mul_pos (inv_pos.mpr (S.penaltyZ_pos β)) (Real.exp_pos _))
  refine ⟨q u,hx u,fun U V => ?_⟩
  calc
    _ = ∑ t, S.likelihood U t*q u := by rw [← Finset.sum_mul,S.chosen h U,one_mul]
    _ ≤ _ := Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hu (mem_univ (S.prediction U t,V)))
      (S.likelihood_pos U t)

theorem bright (T : History G) (H : T.Selected) (N p m) (hm : m≤N) (U) : 0<(T.rep N p m).eval U := by
  induction hm using Nat.decreasingInduction with
  | self => simp_rw [(H.starts N p).2]; exact bare_pos ..
  | of_succ k hk ih =>
    let S := (T.levels.clock.op k p)
    let R := T.rep N p (k+1)
    obtain ⟨D,hD,h⟩ := bright_kernel S R.beta (T.levels.blocks k p).branches
    let f x := S.density R.beta x U * R.eval x
    have hp x : 0<f x := mul_pos (lt_of_lt_of_le hD (h x U)) (ih x)
    rw [(H.steps N p k hk).1]
    have he := StepData.push_slice (T.levels.transition_mass k p R.beta) U R.eval
      ((R.envelope (H.represents N p (k+1) hk).good).integrable _)
    refine (integral_pos_iff_support_of_nonneg (show 0 ≤ f from fun x => (hp x).le) he).mpr ?_
    rw [show Function.support f=univ from Set.eq_univ_of_forall fun x => (hp x).ne']
    simp

variable (C : Family G) (h : C.Makes) (d N p k m : ℕ)

def placard {m : ℕ} (hp : m ≤ N) (o : Site (C.side m p)) : (C.path.rep N p m).activities.Moves 1 o :=
    Classical.choice ((h.wilson.represents N p m hp).good.labels.moves 1 o)

/-- translated-coefficient presentation exactly at offset o. Shift ONLY
supports and measured addresses in blocks; coefficient x retained. -/
def aboard (hp : m ≤ N) (o : Site (C.side m p)) (v : C.label d) :=
    let M := C.factory d N p
    stamp o (placard C h N p hp o) (M.entries m (M.terminal.symm v))

structure Train (hp : C.ref d ≤ k) (hi : k ≤ N) (o : Site (C.side k p)) : Prop where
  reads m (hM : k ≤ m) (hN : m≤N) v :
    let H := C.path
    let R := H.rep N p m
    let t := Mix.camp C p k m o
    let P := aboard C h d N p m hN t v
    P.x=Charts.window C h d m N p v ∧ P.Format t C.params R ∧
      P.remBound t R (Real.sqrt (H.levels.clock.forcedAllowance m)) ((H.levels.params m).columns *
        (C.labels.level d).coeffSize ((C.labels.level d).core (Charts.window C h d m N p v)))
  flies m (hM : k ≤ m) (hN : m < N) v :
    let a := Mix.camp C p k m o
    let b := Mix.camp C p k (m+1) o
    (aboard C h d N p m (by omega) a v).density a (C.localSection d) (C.path.rep N p m)=
       blast C.path N p m d ((aboard C h d N p (m+1) (by omega) b v).density b (C.localSection d) (C.path.rep N p (m+1)))
  shows v U :
    let a := Mix.camp C p k N o
    (aboard C h d N p N le_rfl a v).density a (C.localSection d) (C.path.rep N p N) U=
      (C.S.a N:ℂ)^d * ((C.path.rep N p N).eval U:ℂ) * C.O N p v a U

lemma begin_anchor (o : Site (C.side k p)) : Mix.camp C p k k o=o := by
  rw [Mix.camp, dif_pos le_rfl]
  simp [Schedule.toDepth,Ratio.embed,Schedule.steps]



end YM.Extra.Histories.Tour
