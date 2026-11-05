import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.Post
import YM.Next.SCHEDULE.Support

/-!
# Another support charge: changing cover radii on the weak restart

KRcov  at the SAME lattice, not a foreshortening of the lattice.
Use even on supports with winding. Prove the quantitative estimate with new
halo too, and the separate NO-loss estimate when not charging a halo. Thus
E family norms are compatible even at the SAME vacuum exponent when switching
once to new masks (not equality of those masked terms! Exact compensation
elsewhere). Complete actual-link supports only. Doesn't bound emergent K or
source H. The displayed shape test is available at every stage by another
post-L gate. Keep thresholds for restarted references fixed while testing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling
open Filter Function RG Lattice Bid Corona Clock Instrument
open scoped Topology

variable {G : Gauge} {n : Side}

lemma cover_earns {A B : ℕ} (h : A ≤ B) (X : Support n) : coverNumber B X ≤ coverNumber A X := by
  obtain ⟨C,H,he⟩:=coverNumber_realized A X; rw [← he]
  refine Corona.list_cost B ⟨fun x hx => halo_mono h (Finset.Subset.refl C) (H.1 hx),ship_halo B ?_⟩
  have hv:=halo_ship _ H.2
  intro x hx y hy; apply Relation.ReflTransGen.mono ?_ x y (hv _ hx _ hy)
  intro a b hh; exact ⟨hh.1,hh.2.1,hh.2.2.trans (by omega)⟩

open Finset
lemma itinerary (R : ℕ → Site n) (N b : ℕ) (h : ∀ k < N,separation (R k) (R (k+1)) ≤ 1)
    (hp : 1 ≤ b) : ∃ D : Support n, Ships D b ∧ b*D.card ≤ N+b ∧
    ∀ k ≤ N, R k∈halo b D := by
  let f := fun k => R (b*k)
  let D := (range (N/b+1)).image f
  have ht (i) : i≤N/b → b*i ≤ N := fun hi => by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hp).1 hi
  have he (i) (hi : i ≤ N/b) : Relation.ReflTransGen (Touch D b) (f 0) (f i) := by
    apply line_path
    · intro k hk; exact mem_image_of_mem f (mem_range.mpr (by omega))
    intro k hk; refine le_trans (Corona.path_span h (b*k) (b*(k+1)) (by gcongr; omega) (ht _ (by omega))) ?_
    rw [Nat.mul_succ]; omega
  refine ⟨D,fun i hi j hj => ?_,?_,fun k hk => ?_⟩
  · obtain ⟨i,hii,rfl⟩:=mem_image.mp hi; obtain ⟨j,hji,rfl⟩:=mem_image.mp hj
    exact (Corona.sym (he i (show i≤N/b from Nat.lt_succ_iff.mp <| mem_range.mp hii))).trans (he j (Nat.lt_succ_iff.mp <| mem_range.mp hji))
  · calc
      b*D.card ≤ b*(N/b+1) := Nat.mul_le_mul_left _ (Finset.card_image_le.trans (by rw [card_range]))
      _ ≤ _ := by rw [Nat.mul_succ]; exact Nat.add_le_add_right (ht _ le_rfl) _
  refine halo_spec.mpr ⟨f (k/b),mem_image_of_mem f (mem_range.mpr (by
    have hx := Nat.div_le_div_right (c:=b) hk; omega)),?_⟩
  have hx := Nat.mod_add_div k b; have he:=Nat.mod_lt k hp
  apply le_trans (Corona.path_span h _ _ (by omega : b*(k/b) ≤ k) hk) (by omega)












open RG.Supply
variable {s : Survey G} {K : Precision.MapPrices} {q : Quote} {e : ℕ → ℕ → Exchange} {v : ℕ → ℕ}
variable {D : Rolls (s.paper q v)} {Θ : Protection D}

/-- Compatible reset tests. q old/mchorus share explicit formulas.
`D` in hM numerical estimate unconditionally; this is a *post-L*
delay (with radius already bought pre-L).
-/
structure Rearm (x : ℝ) (s : Survey G) (j : ℕ) (e : Exchange) : Prop where
  deals : 0 < x
  save : 2*chorus.t x ≤ plain.t x
  hull : 6*(s.o.A j+e.extra)*e.foot ≤ foundation s e j/2 * (Clock.cover x:ℝ)

private lemma save_late : ∀ᶠ x : ℝ in atTop, 2*chorus.t x ≤ plain.t x := by
  -- compare logs: y^{2}-y^{3/2} eventually ∞
  have he:=clock.eventually_ge_atTop 4
  filter_upwards [he,eventually_gt_atTop (0:ℝ)] with x hx hp
  have hz := gp hp
  unfold Instrument.t
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ hz.le
  unfold P watch plain chorus
  let y:= tick x
  change 2*Real.exp (y^((3:ℝ)/2)) ≤ Real.exp (y^(2:ℝ))
  have hy : 4≤y := hx
  nth_rw 1 [← Real.exp_log (show (2:ℝ)>0 by norm_num)]
  rw [← Real.exp_add]; apply Real.exp_monotone
  have hv := Real.log_le_sub_one_of_pos (show (2:ℝ)>0 by norm_num)
  rw [Real.rpow_two,show (3:ℝ)/2= 1+1/2 by norm_num,Real.rpow_add (by linarith : 0 < y),Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hh := Real.sqrt_nonneg y
  nlinarith [Real.sq_sqrt (by linarith : 0 ≤ y)]

lemma Rearm.cover (s : Survey G) (j) (e : Exchange) : ∀ᶠ x in atTop, Rearm x s j e := by
  have hu := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp Clock.counting
  filter_upwards [eventually_gt_atTop (0:ℝ),save_late, (hu.const_mul_atTop (half_pos (foundation_pos s e j))).eventually_ge_atTop
    (6*(s.o.A j+e.extra)*e.foot)] with x hx hh hm
  exact ⟨hx,hh,hm⟩

def Bumper (e : ℕ → ℕ → Exchange) (W : Delays Θ) := ∀ j,∀ x ≥ W.betaEntry j, Rearm x s j (e j j)

lemma Bumper.bump (e) (W : Delays Θ) : ∃ V, Boost W V ∧ Bumper e V := by
  choose x hx using fun i => eventually_atTop.1 (Rearm.cover s i (e i i))
  let V : Delays Θ := { W with betaEntry := fun j => max (W.betaEntry j) (x j) }
  exact ⟨V,⟨fun i => le_max_left ..,le_rfl,le_rfl,le_rfl⟩,fun i b hh => hx i b (le_trans (le_max_right ..) hh)⟩


end YM.Next.Scheduling
