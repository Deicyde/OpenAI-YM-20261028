import YM.FullVolume.Artes.Events
import YM.Extra.WILSON_STARTUP.Roll
/-! Extend the actual finance of Builder boundary metrics; preserve T. -/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Change
open Matrix Function Filter RG Wilson Lattice Bid Precision Exterior Bloch Tree Work Design Polar F08
open scoped BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {a : Levels G} {M H : Horizon a} {K : MapPrices}
variable {n f L : Side} {S : StepData n f} {B C : Bed} {p q : Clip} {η Ω : ℝ} {U : Towers L}

theorem springboard (C : Supply.Sheet G) (K : MapPrices) : ∃ K' : MapPrices, ∀ (a : Levels G), a.clock.stage=C.profile →
    (∀ N,(a.params N).clip.direct ≤ 1) → ∀ M : Horizon a, M.Suffices K → ∃ H : Horizon a, H.Suffices K' ∧ Overlay H M ∧ (∀ N m, m+1<N→ H.towers N m=M.towers N m) ∧ ∀ N m,m<N → (H.towers N m).T=(M.towers N m).T := by
  choose t v ht hf using fun i => spin_cost (C.profile i).clip (K.α i) (K.Ω i) (K.alpha_pos i)
  let K' : MapPrices := {
    α := fun i => min (K.α i) (t i)
    alpha_pos := fun i => lt_min (K.alpha_pos i) (ht i)
    Ω := fun i => max 1 (max (K.Ω i) (v i))
    η := fun i => min 1 (K.η i)
    eta_pos := fun i => lt_min one_pos (K.eta_pos i) }
  refine ⟨K', fun a ha hg M hM => ?_⟩
  let H := mapped M
  have h := overlaid M
  have ha' (N : ℕ) : C.profile (a.clock.J N) = a.params N := congr_fun ha.symm _
  choose X hX using fun N : ℕ => hf (a.clock.J N) (M.H N N) (by rw [ha']; exact hg N) ((hM.rows N N le_rfl).2.2.2.1)
  let T := fun (N m : ℕ) => if m+1=N then spin (X (m+1)) (M.towers N m) else M.towers N m
  have hT N m : (T N m).A0=(M.towers N m).A0 ∧ (T N m).T=(M.towers N m).T := by unfold T; split <;> exact ⟨rfl,rfl⟩
  have hm i : K.Ω i ≤ K'.Ω i := (le_max_left ..).trans (le_max_right ..)
  have he i : v i ≤ K'.Ω i := (le_max_right ..).trans (le_max_right ..)
  refine ⟨⟨H.H,T⟩,⟨fun N m hx => ?_,fun N m hx n => ?_,fun N m hx => ?_,fun N m p hx => ?_,fun N m p hx => ?_,fun N n => ?_⟩,
    ⟨h.peak,h.other,fun N m _ => (hT N m).1⟩, (fun N m h=>if_neg (by omega)), (fun N m _=> (hT N m).2)⟩
  · obtain hx|rfl := lt_or_eq_of_le hx
    · dsimp only; rw [h.other N m hx]; exact covered_mono (hM.rows _ _ hx.le) (min_le_left ..) (hm _)
    dsimp only; rw [h.peak]; exact Design.covered _ (hg m) (le_max_left ..)
  · dsimp only; obtain hx|rfl := lt_or_eq_of_le hx
    · rw [h.other N m hx]; exact floor_mono (hM.all _ _ hx.le n) (min_le_right ..) (hm _)
    rw [h.peak]; exact Design.level _ (hg m) _ (min_le_left ..) (le_max_left ..)
  · change (T N m).Deep _ _ _
    unfold T; obtain hq|rfl := lt_or_eq_of_le (a:=m+1) (b:=N) hx
    · rw [if_neg hq.ne]; exact deep_mono _ (hM.costs N m hx) (min_le_left ..) (hm _)
    rw [if_pos rfl]; exact deep_mono _ (hX (m+1) _ _ _ (hM.costs _ _ hx) |>.1) (min_le_right ..) (he _)
  · dsimp only; rw [h.other _ _ hx]
    have hu : Towers.Diagonal (a.clock.op m p) (M.H N (m+1)) (M.H N m) (T N m) := by
      obtain ⟨e1,e2,e3⟩ := hM.crossings N m p hx
      constructor <;> simpa only [(hT N m).1,(hT N m).2]
    obtain hq|rfl := lt_or_eq_of_le (a:=m+1) (b:=N) hx
    · rw [h.other _ _ hq]; exact hu
    rw [h.peak]; exact top_diagonal hu (hM.all _ _ hx _) (hM.top _ _)
  · dsimp only; rw [h.other _ _ hx]; unfold T; obtain hq|rfl := lt_or_eq_of_le (a:=m+1) (b:=N) hx
    · rw [if_neg hq.ne,h.other _ _ hq]; exact hM.stack _ _ _ hx
    rw [if_pos rfl,h.peak]
    obtain ⟨hL,hR,h⟩ := (hX (m+1) _ _ _ (hM.costs _ _ hx)).2 _ _ (a.clock.op m p).sizes
    rw [ha'] at h
    exact trans_roll (hM.stack _ _ _ hx) hL hR (h _ _ (hM.all _ _ hx _) (hM.top _ _))
  change (H.H N N).diagonal.acts n = 1
  rw [overlaid M |>.peak]; simp only [bed,spike_acts,one_smul]
end YM.WilsonStartup.Change
