import YM.Next.UV_STRESS.Insides
import YM.Org.Input


/-!
# Shrinking actual dependence cone inside centered reflection cubes

Constants from the operation only J growth and L≥3. No repeated-step loss
per arbitrarily-fine m; applies even across stages and uniformly in p.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Set Function Filter MeasureTheory Analysis Lattice Wilson RG Cells
open scoped Topology BigOperators
variable {G : Gauge} {c f : Side} (S : StepData c f)

/-- origin cube in native steps on the actual torus. -/
def region (n : Side) (r : ℕ) := wrap n '' (↑(box r):Set Cover)

lemma travel_shadow (r : ℕ) : shadow S (region c r) ⊆ region f (S.patch.L.val*r+9*S.patch.radius) := by
  rintro y ⟨x,⟨v,hv,rfl⟩,z,hz,rfl⟩
  let L := S.patch.L.val
  refine ⟨z+ L • v, ?_,?_⟩
  · obtain ⟨A,B⟩ := box_test.mp hz
    obtain ⟨p,q⟩ := box_test.mp (show v∈box _ from hv)
    change _∈box (L*r+9*S.patch.radius)
    have he i : -(↑(L*r+9*S.patch.radius) : ℤ) ≤ z i+(L:ℤ)*v i ∧ z i+(L:ℤ)*v i ≤ ↑(L*r+9*S.patch.radius : ℕ) := by
      have hw : (0:ℤ) ≤ L := by exact_mod_cast Nat.zero_le _
      specialize A i; specialize B i; push_cast at *
      constructor <;> linarith [mul_le_mul_of_nonneg_left (p i) hw,mul_le_mul_of_nonneg_left (q i) hw]
    apply box_test.mpr; exact ⟨fun i => by simpa using (he i).1,fun i => by simpa using (he i).2⟩
  rw [map_add, S.ratio.embed_wrap]; rfl

variable (C : Family G) (r : ℕ)

-- before `k` value unused

def advanceSize (k r : ℕ) : ℕ → ℕ
  | 0 => r
  | m+1 => if k≤m then (C.S.block m).val*advanceSize k r m + 9*((C.path.levels.clock.op m 0).patch.radius) else r

lemma first_radius (k) : advanceSize C k r k=r := by cases k <;> simp [advanceSize]
lemma next_radius (p k m) (h : k ≤ m) : advanceSize C k r (m+1) =
    (C.S.block m).val*advanceSize C k r m + 9*((C.path.levels.clock.op m p).patch.radius) := by
  simp only [advanceSize,if_pos h]; rfl

def available (k m r : ℕ) := C.S.a m * (advanceSize C k r m + 24*((C.path.levels.clock.J m:ℝ)+4))

theorem squeezed_steps (k m : ℕ) (h : k≤m) : available C k m r ≤ available C k k r := by
  induction m,h using Nat.le_induction with
  | base => rfl
  | succ m H IH =>
    let L := (C.S.block m).val
    let a := C.S.a (m+1)
    let B := C.path.levels.clock
    have hh : C.S.a m=a*(L:ℝ) := (C.S.embeds_scale (C.S.oneStep m 0)).symm
    refine le_trans ?_ IH; unfold available
    rw [next_radius C r 0 k m H,hh, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (C.S.a_pos _).le
    have hJ : (B.J (m+1):ℝ) ≤ (B.J m:ℝ)+1 := by exact_mod_cast C.path.levels.fits.stepSlow m
    have hL : (3:ℝ)≤ L := by exact_mod_cast C.S.block_large m
    change (↑(L*advanceSize C k r m+9*((B.J (m+1)+3)*L)):ℝ)+24*(B.J (m+1)+4) ≤ ↑L *(advanceSize _ _ _ _+24*(B.J m+4))
    push_cast
    nlinarith [(show 0 ≤ (B.J m:ℝ) by positivity)]

theorem avoids_edges : Tendsto (fun k => available C k k r) atTop (𝓝 0) := by
  let f := fun k => available C k k r
  have hF k : f k=C.S.a k*(r+24*((C.path.levels.clock.J k:ℝ)+4)) := by simp only [f,available,first_radius]
  have ht k : f (k+1) ≤ (1/2 : ℝ)*f k := by
    rw [hF,hF]
    let L := (C.S.block k).val
    let B := C.path.levels.clock
    have hh : C.S.a k=C.S.a (k+1)*(L:ℝ) := (C.S.embeds_scale (C.S.oneStep k 0)).symm
    rw [hh,mul_assoc, mul_left_comm]; apply mul_le_mul_of_nonneg_left _ (C.S.a_pos _).le
    have hJ : (B.J (k+1):ℝ) ≤ (B.J k:ℝ)+1 := by exact_mod_cast C.path.levels.fits.stepSlow k
    have hL : (3:ℝ)≤ L := by exact_mod_cast C.S.block_large k
    let Z := r+24*((B.J k:ℝ)+4)
    have hz : 96≤Z := by dsimp [Z]; linarith [(show 0 ≤ (B.J k:ℝ) by positivity)]
    change r+24*((B.J (k+1):ℝ)+4) ≤ (1/2 : ℝ)*(L*Z)
    nlinarith [show r+24*((B.J (k+1):ℝ)+4) ≤ Z+24 by dsimp [Z]; linarith]
  have hv k : f k ≤ ((1/2 : ℝ)^k)*f 0 := by
    induction k with
    | zero => simp
    | succ k IH => rw [pow_succ',mul_assoc]; exact (ht k).trans (mul_le_mul_of_nonneg_left IH (by norm_num))
  exact squeeze_zero (fun k => by
    change 0 ≤ f k; rw [hF]; exact mul_nonneg (C.S.a_pos _).le (by positivity)) hv
    (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (show (0:ℝ)≤1/2 by norm_num) (by norm_num)).mul_const (f 0))

lemma in_cube {k m : ℕ} (h : k ≤ m) (p : ℕ) (r : ℕ) (ht : 2*r < Cells.span C.S h p) :
    region (C.side m p) r ⊆ (center C.S p h 0).chamber 0 := by
  rintro x ⟨z,hz,rfl⟩ i
  let T := center C.S p h 0
  let L := T.side.val
  obtain ⟨A,B⟩ := box_test.mp (show z∈box _ from hz); specialize A i; specialize B i
  change ZMod.val (((z i):Per (C.side m p)) - (T.starts 0) i) < L
  rw [T.starts_zero]; change ZMod.val (((z i):Per (C.side m p)) - (0 - ((↑(L/2 : ℕ)) : Per (C.side m p)))) < L
  have hp : L < (C.side m p).val := T.narrow
  change 2*r<L at ht
  let q : ℤ := z i + (↑(L/2 : ℕ):ℤ)
  have hh : 0 ≤ q := by unfold q; omega
  have hV : q < (L:ℤ) := by unfold q; omega
  have he : q.natAbs<L := by omega
  rw [sub_sub_eq_add_sub, sub_zero, show (((L/2:ℕ):ℕ):Per _) =
    (((↑(L/2:ℕ):ℤ):Per (C.side m p))) from (Int.cast_natCast _).symm, ← Int.cast_add,
    show (↑q:Per _)=(q.natAbs : Per (C.side m p)) by
      calc _ = (((q.natAbs:ℤ)): Per _) := congr_arg (fun z : ℤ => (z : Per _)) (by omega)
           _ = _ := Int.cast_natCast _, ZMod.val_natCast_of_lt (he.trans hp)]; exact he

/-- Uniform open space for every subsequent cutoff k ≤ m ≤ N, including
the worst initial level. k chosen after h (h-grid arbitrary). -/
lemma sufficient (h : ℕ) : ∀ᶠ k in atTop, ∃ H : h ≤ k,∀ m p (ht : k≤m),
    region (C.side m p) (advanceSize C k r m) ⊆ (center C.S p (H.trans ht) 0).chamber 0 := by
  have he : Tendsto (fun k => 2*available C k k r) atTop (𝓝 0) := by
    simpa using (avoids_edges C r).const_mul (2:ℝ)
  filter_upwards [he.eventually (gt_mem_nhds (C.S.a_pos h)),eventually_ge_atTop h] with k hk hp
  refine ⟨hp,fun m p hm => in_cube C (hp.trans hm) p _ ?_⟩
  apply (Nat.cast_lt (α:=ℝ)).1; apply lt_of_mul_lt_mul_left _ (C.S.a_pos m).le
  push_cast; rw [show C.S.a m * Cells.span C.S (hp.trans hm) p = _ from C.S.embeds_scale ..]
  have ht : C.S.a m*(advanceSize C k r m:ℝ) ≤ available C k m r := by
    unfold available; apply mul_le_mul_of_nonneg_left _ (C.S.a_pos _).le; exact le_add_of_nonneg_right (by positivity)
  linarith [squeezed_steps C r k m hm]
end YM.Next.UVStress
