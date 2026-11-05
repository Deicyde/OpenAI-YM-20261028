import YM.Shoot.Race

/-! Uniform-real-nearby shooting, BEFORE any derivative bounds on the step.

With this purchase even the whole trajectory on the retained interval of
bare β's can be kept with label continuity (a `Curve` at every level). Thus
the `one step` assertions aren't a matter of prescribing a different schedule
when asking if one can shoot to a perturbed b. This is a statement about
**forward** curves only. Doesn't say the *inverse* is a function, not even on
the retained interval. Also demonstrates quantitatively that arbitrary
successful real trials under the prescribed Recipe with its *full* bands but
narrow b are forced to visit strict interiors all the way.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Lattice Wilson RG Shoot Set Function
open scoped Topology
variable {G : Gauge} {a : Levels G} (R : Recipe a)

def low (a : Levels G) (m : ℕ) := 3/4*a.clock.bar + 5/8*G.slopeConstant*a.S.scale m
def high (a : Levels G) (m : ℕ) := 5/4*a.clock.bar + 3/2*G.slopeConstant*a.S.scale m

def nearby (a : Levels G) : Set ℝ := Icc (low a 0) (high a 0)
theorem centers (a : Levels G) : a.clock.bar ∈ interior (nearby a) := by
  rw [nearby, interior_Icc]
  change _ < _ ∧ _ < _
  simp only [low,high,Schedule.scale_zero,mul_zero,add_zero]
  constructor <;> linarith [a.clock.bar_pos]

lemma fits (h : G.Simple) (m) : low a m ≤ high a m ∧ Icc (low a m) (high a m) ⊆ band a m := by
  unfold low high band Calendar.hatBeta
  have ht := mul_nonneg (Gauge.slopeConstant_pos h).le (scale_nn a m)
  have hK := a.clock.bar_pos
  change 0≤ G.slopeConstant * a.clock.schedule.scale m at ht
  change _ ≤ _ ∧ _ -- a.S
  simp only [Levels.S]
  exact ⟨by linarith, Icc_subset_Icc (by linarith) (by linarith)⟩

lemma deep_margin (ht : Drifting a) (p N : ℕ) (t : Trail a p)
    (hr : Competes R p N 0 t) (hw : (t 0).beta ∈ nearby a) (m : ℕ) (hm : m ≤ N) :
    3/4 * a.clock.hatBeta m ≤ (t m).beta ∧ (t m).beta ≤ 5/4 * a.clock.hatBeta m := by
  induction m with
  | zero =>
    change (low a 0 ≤ _ ∧ _ ≤ high a 0) at hw
    simpa [Calendar.hatBeta,low,high] using hw
  | succ i ih =>
    have ht := (div_le_iff₀ (c:=Real.log (a.S.block i).val)
      (Real.log_pos (by exact_mod_cast (show 1 < (a.S.block i).val from lt_of_lt_of_le (by norm_num) (a.S.block_large i))))).mp (ht i)
    obtain ⟨hv,hp⟩:=ih (by omega)
    have hs : a.clock.hatBeta (i+1) = a.clock.hatBeta i + G.slopeConstant*Real.log (a.S.block i).val:=by
      unfold Calendar.hatBeta; rw [Schedule.scale_succ]; unfold Levels.S; ring
    obtain ⟨ho,hn⟩:=abs_le.mp (hr.persists _ (Nat.zero_le _) hm).drift
    rw [hs]; constructor <;> linarith

/-- Cutoff/p fixed; entire forward shooting arc with label charges &
startup. Does not constrain t outside this interval. -/
structure Arc (p N m) where
  left : ℝ
  right : ℝ
  replay : ℝ → Trail a p
  nonempty : left ≤ right
  trials : ∀ x∈Icc left right, Competes R p N m (replay x)
  top : ∀ x∈Icc left right,(replay x N).beta=x
  priced i : m ≤ i → i ≤ N → Curve (a.budget i) (fun x => replay x i) (Icc left right)
  lower : (replay left m).beta=low a m
  upper : (replay right m).beta=high a m

namespace Arc
variable {R}
lemma covers {p N} (Y : Arc R p N 0) : nearby a ⊆ (fun x => (Y.replay x 0).beta) '' Icc Y.left Y.right := by
  have hx := intermediate_value_Icc Y.nonempty (Y.priced 0 le_rfl (Nat.zero_le _)).beta
  rwa [Y.lower,Y.upper] at hx

private lemma crosses (h : G.Simple) (K : Drifting a) {N p i : ℕ} {u v} (hu : R.Relays N i p u v) :
    (v.beta=low a (i+1) → u.beta<low a i) ∧ (v.beta=high a (i+1) → high a i < u.beta) := by
  have hz : 0 < Real.log (a.S.block i).val := Real.log_pos (by exact_mod_cast (show 1 < (a.S.block i).val from lt_of_lt_of_le (by norm_num) (a.S.block_large i)))
  obtain ⟨he,hx⟩:=abs_le.mp hu.drift
  have hp := (div_le_iff₀ hz).mp (K i)
  have hf := mul_pos (Gauge.slopeConstant_pos h) hz
  unfold low high; rw [Schedule.scale_succ]
  constructor <;> intro hu <;> linarith

private def pad (a : Levels G) (R : Recipe a) (p N m : ℕ) : Rep G (a.S.side m p) :=
  { path := R.path N m
    clip := (a.params m).clip
    activities := { reg := fun _ => ⟨0,{0},by simp⟩
                    forced := fun _ => ⟨{0},{0},by simp, le_rfl, fun _ => True⟩
                    E := 0
                    K := 0 }
    p := a.budget m
    beta := 1
    v := 0 }

theorem bought (p N) (hh : R.Issues N p) (h : G.Simple) (H : Drifting a) (m : ℕ) (hm : m ≤ N) : Nonempty (Arc R p N m):=by
  induction hm using Nat.decreasingInduction with
  | self =>
    obtain ⟨F,hF,hX⟩:=hh.initial; set f:=fun x : ℝ=> update (pad a R p N) N (F x); have hf (x): f x N=F x:=update_self ..
    obtain ⟨hu,ht⟩:= fits (a:=a) h N
    refine ⟨⟨_,_,f,hu,fun x hx=>?_,fun x hx=>hf x ▸ (hX _ (ht hx)).1, fun i hi hi'=>?_,?_,?_⟩⟩
    · refine ⟨fun i hi hj=> ?_, (hf x).symm ▸ (hX _ (ht hx)).2.2,fun i hi hj=>by omega⟩
      rw [Nat.le_antisymm hj hi,hf]; have he:=hX _ (ht hx); exact ⟨he.2.1,he.1.symm ▸ ht hx⟩
    · have h := Nat.le_antisymm hi hi'; subst i; simp_rw [hf]; exact hF.mono ht
    · rw [hf,(hX _ (ht (left_mem_Icc.mpr hu))).1]
    rw [hf,(hX _ (ht (right_mem_Icc.mpr hu))).1]
  | of_succ k hk hT =>
    obtain ⟨W⟩ := hT
    obtain ⟨T,ht,hq⟩ := hh.advances k hk W.left W.right W.nonempty
      (fun x=> W.replay x (k+1)) (W.priced _ le_rfl hk) (fun x hx=> (W.trials x hx).prices _ le_rfl hk)
    have hp:= ((crosses h H (hq _ (left_mem_Icc.mpr W.nonempty)).2).1 W.lower)
    have hP:= ((crosses h H (hq _ (right_mem_Icc.mpr W.nonempty)).2).2 W.upper)
    obtain ⟨l,hl,u,hu,hl',hu',hX⟩:= narrow W.nonempty ht.beta hp.le (fits h k (a:=a)).1 hP.le
    let F:= fun x : ℝ=> update (W.replay x) k (T x)
    have hv (x): F x k=T x:=update_self ..
    have hy (x i) (hi : k < i): F x i=W.replay x i:= update_of_ne (Nat.ne_of_gt hi) ..
    have he : Icc l u ⊆ Icc W.left W.right:= Icc_subset_Icc hl.1 hu.2
    refine ⟨⟨l,u,F,hu.1,fun x hx=>?_,fun x hx=>by rw [hy x N hk,W.top _ (he hx)],fun i hi hi'=>?_,by rw [hv,hl'],by rw [hv,hu']⟩⟩
    · have ho:= W.trials x (he hx)
      refine ⟨fun i hi hj=> ?_,by rw [hy x N hk]; exact ho.fromTop,fun i hi hj=>?_⟩
      · rcases eq_or_lt_of_le hi with rfl|hi
        · rw [hv]; exact ⟨(hq x (he hx)).1,(fits (a:=a) h _).2 (hX hx)⟩
        rw [hy _ _ hi]; exact ho.prices _ hi hj
      rcases eq_or_lt_of_le hi with rfl|hi
      · rw [hv,hy _ _ (Nat.lt_succ_self _)]; exact (hq x (he hx)).2
      rw [hy _ _ hi,hy _ _ (by omega)]; exact ho.persists _ hi hj
    rcases eq_or_lt_of_le hi with rfl|hi
    · simp_rw [hv]; exact ht.mono he
    simp_rw [hy _ _ hi]; exact (W.priced i hi hi').mono he
end Arc
end YM.FullVolume
