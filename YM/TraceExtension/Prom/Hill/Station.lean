import YM.Next.RANK.Station
/-!
  Changing block factor: exact affine scale stops on the original Schedule.
  Variant of YM.Next.RANK.Station for dynamic stops.
  `Permitted` bounds stages (on pos k and bracket Credit.
  No equality of neighboring factors or branch data.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Station
open Lattice Wilson RG Extraction Cells
open scoped Classical BigOperators Topology
variable {G : Gauge}

def gainSky (T : Schedule) (i : ℕ) (r : ℝ) : ℕ :=
  ((Finset.range (i+1)).filter (fun j=> r ≤ T.a j/T.a i)).sup id

lemma gain_under (T : Schedule) (i : ℕ) (r : ℝ) : gainSky T i r ≤ i := by
  apply Finset.sup_le; intro j hj
  obtain ⟨hZ,hP⟩:= Finset.mem_filter.mp hj; apply Nat.le_of_lt_succ (Finset.mem_range.mp hZ)
lemma gain_fee {T : Schedule} {i j:ℕ}{r:ℝ}(h : j ≤ i)(hx : r ≤ T.a j/T.a i) : j ≤ gainSky T i r :=
  Finset.le_sup (f:=id) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le h),hx⟩)
lemma gain_high {T : Schedule}{i j:ℕ}{r:ℝ}(h : j ≤ i)(hx : r ≤ T.a j/T.a i) :
    r ≤ T.a (gainSky T i r)/T.a i:=by
  let z:= ((Finset.range (i+1)).filter (fun j=> r ≤ T.a j/T.a i)); have he : z.Nonempty:=⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le h),hx⟩⟩
  let m:= z.max' he
  have ht : r ≤ T.a m/T.a i:= (Finset.mem_filter.mp (Finset.max'_mem z he)).2
  suffices g : m=gainSky T i r by rwa [←g]
  refine le_antisymm (Finset.le_sup (f:=id) (Finset.max'_mem z he)) (Finset.sup_le fun b h'=> Finset.le_max' _ _ h')

def middleSky (A : Levels G) (b : ℝ) (k : ℕ) := gainSky A.S k (mag A b k*A.clock.monitor k^2)
def widthSky (A : Levels G) (b : ℝ) (k : ℕ) := gainSky A.S (middleSky A b k) ((A.clock.coverSize k:ℝ)^10)

def leastL (A : Levels G) (k : ℕ) := min (A.clock.factor (A.clock.J k)) (A.clock.factor (A.clock.J k-1))
def wheelSky (A : Levels G) (k : ℕ) : ℝ:= (leastL A k).val

lemma beforeSky (A : Levels G) (b : ℝ) (k : ℕ) : middleSky A b k ≤ k := gain_under ..
lemma widerSky (A : Levels G) (b : ℝ) (k : ℕ) : widthSky A b k ≤ middleSky A b k := gain_under ..

variable (A : Levels G) (b : ℝ)

structure AllowedSky (k : ℕ) : Prop where
  dilation : mag A b k * A.clock.monitor k ^ 2 ≤ A.S.a (middleSky A b k) / A.S.a k
  depth : (A.clock.coverSize k:ℝ)^(10:ℕ) ≤ A.S.a (widthSky A b k)/A.S.a (middleSky A b k)
  large : (2:ℝ) ≤ wheelSky A k
  bracket (m : ℕ) : widthSky A b k ≤ m → m ≤ k → A.clock.J k -1 ≤ A.clock.J m

namespace AllowedSky
variable {A b k} (h : AllowedSky A b k)
include h
lemma ell (j : ℕ) (hl : widthSky A b k ≤ j) (he : j ≤ k) : wheelSky A k ≤ wheel A j:= by
  have hx := h.bracket j hl he; have hw := A.fits.mono he
  change A.clock.J j ≤ A.clock.J k at hw
  have ht : leastL A k ≤ A.clock.factor (A.clock.J j):= by
    rcases eq_or_lt_of_le hw with hr|hr
    · rw [hr]; exact min_le_left ..
    rw [show A.clock.J j=A.clock.J k-1 by omega]; exact min_le_right ..
  exact Nat.cast_le.mpr ht
lemma blocks (i : ℕ) (hh : widthSky A b k ≤ i) (hp : i<k) : wheelSky A k ≤ ((A.S.block i).val:ℝ) := by
  rw [← A.fits.sameFactor i]; apply h.ell; omega; omega
lemma scales (m j : ℕ) (he : widthSky A b k ≤ m) (hr : m ≤ j) (hp : j≤k) :
    (wheelSky A k)^(j-m) ≤ A.S.a m/A.S.a j := by
  induction j,hr using Nat.le_induction with
  | base => rw [div_self (A.S.a_pos _).ne', Nat.sub_self,pow_zero]
  | succ j hj ih =>
    rw [show j+1-m=j-m+1 by omega, pow_succ, A.S.a_step, div_div_eq_mul_div]; rw [mul_comm (A.S.a m), mul_div_assoc, mul_comm (↑(A.S.block j).val:ℝ)]
    exact mul_le_mul (ih (by omega)) (h.blocks j (he.trans hj) hp) (le_trans (by norm_num) h.large) (div_nonneg (A.S.a_pos _).le (A.S.a_pos _).le)
lemma delta (p : ℕ) (m j : ℕ) (_he : widthSky A b k ≤ m) (hr : m≤j) (_hp : j≤k) :
    ((A.S.toDepth hr p).count.val:ℝ)=A.S.a m/A.S.a j := by
  let Y:=A.S.toDepth hr p; rw [eq_div_iff (A.S.a_pos _).ne',mul_comm,A.S.embeds_scale Y]
lemma surplusage (p : ℕ) : (A.clock.coverSize k)^(10:ℕ) ≤ (A.S.toDepth (widerSky A b k) p).count.val := by
  have he:= h.depth
  rw [← h.delta p _ _ le_rfl (widerSky A b k) (beforeSky ..)] at he; exact_mod_cast he
lemma gain_bump (i j : ℕ) (hi : i ≤ k) (hr : Station.widthSky A b k ≤ j)
    {r : ℝ} (hs : 0 < r) (hx : j=gainSky A.S i r) : i-j ≤ want (wheelSky A k) r:= by
  let u:= want (wheelSky A k) r
  by_contra! hn; have he : j< i-u:= by omega
  have hQ : r ≤ wheelSky A k^u:= (wanted (by linarith only [h.large]) hs _).2 le_rfl
  apply lt_irrefl (i-u); apply lt_of_le_of_lt _ he; conv_rhs =>rw [hx];
  refine gain_fee (Nat.sub_le ..) (hQ.trans ?_); conv_lhs =>rw [show u=i-(i-u) by omega];
  exact h.scales (i-u) i (hr.trans he.le) (Nat.sub_le ..) hi
lemma full : k-middleSky A b k ≤ bump (wheelSky A k) b (A.clock.hatBeta k) :=
  h.gain_bump _ _ le_rfl (widerSky ..) (mul_pos (mag_pos ..) (pow_pos (Real.exp_pos _) _)) rfl
lemma shift : middleSky A b k-widthSky A b k≤more (wheelSky A k) (A.clock.hatBeta k) := by
  have he : (0:ℝ)< (A.clock.coverSize k:ℝ) := by exact_mod_cast (A.budget k).B_pos
  exact h.gain_bump _ _ (beforeSky ..) le_rfl (pow_pos he 10) rfl
end AllowedSky
end YM.Next.Rank.Station
