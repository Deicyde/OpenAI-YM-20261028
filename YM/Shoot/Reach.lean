import YM.Shoot.Criteria

/-!
# No projection discontinuity across barriers

E continuity enough on each step even across *closed* ends. Alternative
shooting proof by passing to a nonempty interval with endpoints giving full
next barrier and surviving gains on the entire interval. Do not extend a
representation outside its survival interval and claim norm continuity there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG.Shoot
open Lattice Supply Wilson Filter Set Function
open scoped Matrix.Norms.Frobenius BigOperators ContDiff Topology
variable {G : Gauge} {a : Levels G} {R : Recipe a}

lemma narrow {f : ℝ → ℝ} {x y d u : ℝ} (hx : x ≤ y) (hf : ContinuousOn f (Icc x y))
    (ha : f x ≤ d) (hd : d ≤ u) (hb : u ≤ f y) : ∃ z∈Icc x y, ∃ w∈Icc z y,
    f z=d ∧ f w=u ∧ MapsTo f (Icc z w) (Icc d u) := by
  let A := Icc x y ∩ f ⁻¹' {u}
  have he : IsCompact A := isCompact_Icc.of_isClosed_subset (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  obtain ⟨b,hh,hy⟩ := intermediate_value_Icc hx hf (show u∈Icc _ _ from ⟨ha.trans hd,hb⟩)
  let w := sInf A
  have hw : IsLeast A w := he.isLeast_sInf ⟨b,hh,hy⟩
  have wy : w∈Icc x y := hw.1.1
  let B := Icc x w ∩ f ⁻¹' {d}
  have h : ContinuousOn f (Icc x w) := hf.mono (Icc_subset_Icc_right wy.2)
  have H : IsCompact B := isCompact_Icc.of_isClosed_subset (h.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  have wu : f w=u := hw.1.2
  obtain ⟨b',hh',hy'⟩ := intermediate_value_Icc wy.1 h (show d∈Icc _ _ from ⟨ha,hd.trans_eq wu.symm⟩)
  let z := sSup B
  have hz : IsGreatest B z := H.isGreatest_sSup ⟨b',hh',hy'⟩
  have zz : z∈Icc x w := hz.1.1
  refine ⟨z,Icc_subset_Icc_right wy.2 zz,w,⟨zz.2,wy.2⟩,hz.1.2,wu,?_⟩
  intro c hc
  by_cases ha : f c<d
  · have H : c∈Icc x w := Icc_subset_Icc_left zz.1 hc
    obtain ⟨b,W,e⟩ := intermediate_value_Icc hc.2 (h.mono (Icc_subset_Icc_left H.1)) (show d∈Icc (f c) (f w) from ⟨ha.le,hd.trans_eq wu.symm⟩)
    have hb : b ≤ z := hz.2 ⟨Icc_subset_Icc_left H.1 W,e⟩
    have hg : c < b := lt_of_le_of_ne W.1 fun he => ha.ne (he ▸ e)
    exact False.elim ((hg.trans_le (hb.trans hc.1)).false)
  refine ⟨le_of_not_gt ha,?_⟩
  by_contra! hu
  have hg := Icc_subset_Icc_left zz.1 hc
  obtain ⟨i,hi,e⟩ := intermediate_value_Icc (show x≤c from zz.1.trans hc.1) (h.mono (Icc_subset_Icc_right hc.2))
      (show u∈Icc (f x) (f c) from ⟨show f x≤u from le_trans ‹f x≤d› hd,hu.le⟩)
  have hj := hw.2 (show i∈A from ⟨Icc_subset_Icc_right (hc.2.trans wy.2) hi, e⟩)
  exact (lt_of_le_of_ne hi.2 (fun hn => hu.ne' (hn ▸ e))).not_ge (hc.2.trans hj)

lemma scale_nn (a : Levels G) (i) : 0 ≤ a.S.scale i := by
  induction i with
  | zero => rw [Schedule.scale_zero]
  | succ i ih =>
    rw [Schedule.scale_succ]; exact add_nonneg ih (Real.log_nonneg (by have h := a.S.block_large i; exact_mod_cast (show 1 ≤ (a.S.block i).val from le_trans (by norm_num) h)))

def floorBeta (a : Levels G) (m) := a.clock.bar + (G.slopeConstant/2)*a.S.scale m
def ceilBeta (a : Levels G) (m) := a.clock.bar + (2*G.slopeConstant)*a.S.scale m

lemma limits (a : Levels G) (h : G.Simple) (i) : floorBeta a i ≤ ceilBeta a i ∧
    Icc (floorBeta a i) (ceilBeta a i) ⊆ band a i := by
  have hn := a.clock.bar_pos
  have hr := Gauge.slopeConstant_pos h
  have hh := mul_nonneg hr.le (scale_nn a i)
  unfold floorBeta ceilBeta band Calendar.hatBeta
  constructor
  · linarith
  exact Icc_subset_Icc (by linarith) (by linarith)

def Drifting (a : Levels G) := ∀ i,
    (a.params (i+1)).drift / Real.log (a.S.block i).val ≤ G.slopeConstant/4

lemma Drifting.pay {p : Sheet G} {w : Rolls p} {T : Protection w} {W : Delays T} {Y : Bar W} {B : Wait Y} (h : Paid B a) :
    Drifting a := by
  intro i
  have hx : p.first ≤ a.clock.J (i+1) := h.firstZero ▸ a.fits.mono (Nat.zero_le (i+1))
  unfold Levels.params Calendar.params
  rw [h.stage,show a.S.block i = w.L (a.clock.J (i+1)) from (a.fits.sameFactor i).symm.trans (congr_fun h.lengths _)]
  exact (w.large _).kick hx

lemma gates {N p i : ℕ} {u v} (hp : R.Relays N i p u v) (h : G.Simple) (hd : Drifting a) :
    (v.beta=floorBeta a (i+1) → u.beta<floorBeta a i) ∧ (v.beta=ceilBeta a (i+1) → ceilBeta a i < u.beta) := by
  have hn : 0 < Real.log (a.S.block i).val := Real.log_pos (by
    have h := a.S.block_large i
    exact_mod_cast (show 1 < (a.S.block i).val from lt_of_lt_of_le (by norm_num) h))
  have hu := abs_le.mp hp.drift
  have ht := (div_le_iff₀ hn).mp (hd i)
  have hy := mul_pos (Gauge.slopeConstant_pos h) hn
  unfold floorBeta ceilBeta; rw [Schedule.scale_succ]
  constructor <;> intro HH <;> linarith

/-- one depth across all represented step data -/
abbrev Trail (a : Levels G) (p : ℕ) := ∀ m : ℕ, Rep G (a.S.side m p)

structure Competes (R : Recipe a) (p N m : ℕ) (t : Trail a p) : Prop where
  prices i : m ≤ i → i ≤ N → Lives R N i p (t i) ∧ (t i).beta∈band a i
  fromTop : R.Starter N p (t N)
  persists i : m ≤ i → i < N → R.Relays N i p (t i) (t (i+1))

/-- Padded outside path after upper level. -/
private def padding (a : Levels G) (R : Recipe a) (p N m : ℕ) : Rep G (a.S.side m p) :=
  { path := R.path N m
    clip := (a.params m).clip
    activities := { reg := fun _ => ⟨0,{0},by simp⟩
                    forced := fun _ => ⟨{0},{0},by simp, le_rfl, fun _ => True⟩
                    E := 0
                    K := 0 }
    p := a.budget m
    beta := 1
    v := 0 }

lemma steps (p N : ℕ) (hh : R.Issues N p) (h : G.Simple) (hA : Drifting a) (m : ℕ) (hm : m ≤ N) :
    ∃ l u : ℝ, l ≤ u ∧ ∃ F : ℝ → Trail a p,
      (∀ x∈Icc l u, Competes R p N m (F x)) ∧
        Curve (a.budget m) (fun x => F x m) (Icc l u) ∧
        (F l m).beta=floorBeta a m ∧ (F u m).beta=ceilBeta a m := by
  induction hm using Nat.decreasingInduction with
  | self =>
    obtain ⟨F,H,ht⟩ := hh.initial
    let t := floorBeta a N; let u := ceilBeta a N
    obtain ⟨h0,h1⟩ := limits a h N
    let f := fun x : ℝ => update (padding a R p N) N (F x)
    have he (x) : f x N=F x := update_self ..
    refine ⟨t,u,h0,f,fun x hx ↦ ?_,?_,?_,?_⟩
    · have hy := ht _ (h1 hx)
      refine ⟨fun i hi hi' => ?_, he x |>.symm ▸ hy.2.2, fun i hi HI => False.elim ((hi.trans_lt HI).false)⟩
      rw [Nat.le_antisymm hi' hi,he]; exact ⟨hy.2.1,hy.1.symm ▸ h1 hx⟩
    · simp only [he]; exact H.mono h1
    · rw [he]; exact (ht _ (h1 (left_mem_Icc.mpr h0))).1
    rw [he]; exact (ht _ (h1 (right_mem_Icc.mpr h0))).1
  | of_succ i ik H =>
    obtain ⟨l,u,hw,F,hb,hc,hl,hu⟩ := H
    obtain ⟨T,ht,HI⟩ := hh.advances i ik l u hw (fun x => F x (i+1)) hc (fun x hx => (hb x hx).prices _ le_rfl ik)
    have hy := ((gates (HI _ (left_mem_Icc.mpr hw)).2 h hA).1 hl)
    have hY := ((gates (HI _ (right_mem_Icc.mpr hw)).2 h hA).2 hu)
    obtain ⟨o,ho,e,he,hea,heb,X⟩ := narrow hw ht.beta hy.le (limits a h i).1 hY.le
    have ht' : Icc o e⊆Icc l u := Icc_subset_Icc ho.1 he.2
    let f := fun x : ℝ => update (F x) i (T x)
    refine ⟨o,e,he.1,f,fun x hx => ?_,?_,?_,?_⟩
    · have ha := ht' hx
      have hi := hb x ha
      have HGG := HI x ha
      have hg : f x i=T x := update_self ..
      have hz (k) (hk : i < k) : f x k=F x k := update_of_ne (Nat.ne_of_gt hk) ..
      refine ⟨fun j hj hj' => ?_,by rw [hz _ ik]; exact hi.fromTop, fun j hj hj' => ?_⟩
      · rcases eq_or_lt_of_le hj with hO|hO
        · subst j; rw [hg]; exact ⟨HGG.1,(limits a h i).2 (X hx)⟩
        rw [hz _ hO]; exact hi.prices _ hO hj'
      rcases eq_or_lt_of_le hj with rfl|hj
      · rw [hg,hz _ (by omega)]; exact HGG.2
      rw [hz _ hj,hz _ (by omega)]; exact hi.persists _ hj hj'
    · simp only [f,update_self]; exact ht.mono ht'
    · simp only [f,update_self]; exact hea
    simp only [f,update_self]; exact heb

lemma successful (p N : ℕ) (hh : R.Issues N p) (h : G.Simple) (hA : Drifting a) :
    ∃ T, Competes R p N 0 T ∧ (T 0).beta=a.clock.bar := by
  obtain ⟨l,b,hl,F,hb,-,H,-⟩ := steps p N hh h hA 0 (Nat.zero_le _)
  exact ⟨F l, hb l (left_mem_Icc.mpr hl), H.trans (by simp [floorBeta])⟩
end YM.RG.Shoot
