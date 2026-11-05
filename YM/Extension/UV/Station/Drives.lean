import YM.Extension.UV.Station.StepBill
/-! Accumulation for changing mesh, over an actual native schedule horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV.Linear
open Function Filter Lattice Laurent Bloch RG Supply Next.Free Metric Precision Exterior Matrix
open scoped Topology BigOperators Classical
variable {G:Gauge} (A:Levels G)
def vehicle (m : ℕ) (h : ℕ→ℝ) : ℕ →ℝ
| 0=>1
| i+1=>vehicle m h i*h (m+i)
def stock (m k:ℕ):=vehicle m (fun i=> ((A.S.block i).val :ℝ)) k
def dose (P:MapPrices) (m k:ℕ):=vehicle m (grip P A) k
lemma stock_succ (m k:ℕ) : stock A m (k+1)=stock A m k*(A.S.block (m+k)).val:=rfl
lemma dose_succ (P:MapPrices) (m k:ℕ): dose A P m (k+1)=dose A P m k*grip P A (m+k):=rfl
lemma stock_one (m k:ℕ):1≤ stock A m k:=by
  induction k with
  | zero=> norm_num [stock,vehicle]
  | succ k hk=> exact one_le_mul_of_one_le_of_one_le hk (by change 1≤ ((A.S.block (m+k)).val:ℝ); exact_mod_cast (Nat.succ_le_of_lt (A.S.block (m+k)).property))
lemma stock_pos (m k):0< stock A m k:=zero_lt_one.trans_le (stock_one A m k)
lemma dose_one (P:MapPrices) (m k):1≤ dose A P m k:=by
  induction k with
  | zero=> exact le_rfl
  | succ k hk=>
    have h : 1≤ grip P A (m+k):=one_le_mul_of_one_le_of_one_le (stone_one P _) (one_le_pow₀ (stone_one P _) (n:=2))
    exact one_le_mul_of_one_le_of_one_le hk (by apply h)
lemma stock_den (m k):stock A m k=(A.S.steps m k).val:=by
  induction k with
  | zero => exact (Eq.symm Nat.cast_one)
  | succ k hk=> rw [stock_succ, hk]; exact Eq.symm (Nat.cast_mul ..)
lemma stock_ratio (m k): stock A m k=((A.S.denominator (m+k)).val:ℝ)/(A.S.denominator m).val := by
 rw [stock_den,A.S.den_add,PNat.mul_coe,Nat.cast_mul]; rw [eq_div_iff (show ((A.S.denominator m).val:ℝ)≠0 by positivity),mul_comm]
lemma stock_large (m):Tendsto (stock A m) atTop atTop:=by
  have hu : StrictMono (fun i:ℕ=> m+i):=by intro i j h; change _+_ < _+_; omega
  have h':= (tendsto_natCast_atTop_atTop.comp (A.S.den_strict.tendsto_atTop.comp hu.tendsto_atTop)).atTop_div_const (r:=((A.S.denominator m).val:ℝ)) (by positivity)
  exact h'.congr (fun i=> (stock_ratio A m i).symm)
lemma dose_bound (P:MapPrices) (hg:∀ i,(grip P A i)^8 ≤ (A.S.block i).val) m k : (dose A P m k)^8 ≤ stock A m k := by
  induction k with
  | zero=> norm_num [dose, stock, vehicle]
  | succ k hk=> rw [dose_succ,stock_succ,mul_pow]; apply mul_le_mul hk (hg _) (by positivity : 0≤grip P A _ ^ 8) (stock_pos ..).le -- parsing

def beamed {A:Levels G} (M : Horizon A) (N p m k:ℕ) (y : ∀ i : ℕ,((Body 1 (A.S.side i p)) →ℝ)):= ∀ i,i<k → y (m+i+1)=plane M N (m+i) p *ᵥ (y (m+i))
section horizon
variable {A} (M : Horizon A) (P:MapPrices) (hp:M.Suffices P)
    (heq : ∀ n m, m<n → (M.towers n m).T=((YM.Next.Free.destination A n m).duo A.clock.kernel.penalty).T)
    (N p m :ℕ) (v:ℝ) (x : ∀ i,Body 1 (A.S.side i p) → ℝ) (hv:0≤v) (z:ℕ)
local notation "curvat" => fun (j:ℕ)=> d 1 (A.S.side j p) *ᵥ x j
include hp hv
set_option maxHeartbeats 500000 in
lemma transport_field (k) (hc:m+k≤N) (hb:beamed M N p m k x) (hx:Bounded (x m) v): Bounded (x (m+k)) (v*dose A P m k/stock A m k):=by
  induction k with
  | zero => simpa [dose,stock,vehicle] using hx
  | succ k hk=>
     have hk' := hk (by omega) (fun i hi=>hb i (by omega))
     have hq : m+(k+1)=m+k+1:=rfl
     rw [hq]; rw [hb k (by omega),dose_succ,stock_succ] -- `at *` syntax
     have h0:=mul_nonneg hv (zero_le_one.trans (dose_one A P m k))
     intro a
     apply (plane_lower M P hp N (m+k) p (by omega) (div_nonneg h0 (stock_pos ..).le) _ hk' a).trans
     have h₀:=stone_one P (A.clock.J (m+k+1))
     have hs := stone_one P (A.clock.J (m+k))
     have hh: stone P (A.clock.J (m+k+1)) ≤ grip P A (m+k):= (by unfold grip; linarith [mul_le_mul_of_nonneg_right hs (by positivity : 0≤ ((stone P (A.clock.J (m+k+1)))^2)),mul_le_mul_of_nonneg_left h₀ (zero_le_one.trans h₀)] -- h0.le wrong direction
         )
     calc _ = stone P (A.clock.J (m+k+1))*(v*dose A P m k)/(stock A m k * (A.S.block _).val):= by ring_nf
          _ ≤ _ := by rw [← mul_assoc v,mul_comm (v * dose A P m k)]; exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh h0) (mul_nonneg (stock_pos ..).le (Nat.cast_nonneg _))

set_option maxHeartbeats 300000 in
lemma transport_curl (k) (hc:m+k≤N) (hb:beamed M N p m k x) (hx: Bounded ((fun j=>d 1 (A.S.side j p) *ᵥ x j) m) v): Bounded (curvat (m+k)) (v*dose A P m k/(stock A m k)^2):=by
  induction k with
  | zero => simpa [dose,stock,vehicle] using hx
  | succ k hk=>
     have hk' := hk (by omega) (fun i hi=>hb i (by omega))
     have hq : m+(k+1)=m+k+1:=rfl
     rw [hq] at *
     dsimp only at * -- expensive?
     rw [hb k (by omega),dose_succ,stock_succ]
     have h₀:=mul_nonneg hv (zero_le_one.trans (dose_one A P m k))
     intro a
     exact (curl_bills M P hp N (m+k) p (by omega) (div_nonneg h₀ (by positivity)) _ hk' a).trans_eq (by ring_nf)

include heq in
set_option maxHeartbeats 500000 in
lemma transport_separation (k) (hc:m+k≤N) (hb:beamed M N p m k x) (hx:varied ((fun j=> d 1 (A.S.side j p) *ᵥ x j) m) v): varied (curvat (m+k)) (v*dose A P m k/(stock A m k)^3):=by
  induction k with
  | zero => simpa [dose,stock,vehicle] using hx
  | succ k hk=>
     have hk' := hk (by omega) (fun i hi=>hb i (by omega))
     have hq : m+(k+1)=m+k+1:=rfl
     rw [hq]; dsimp only
     rw [hb k (by omega),dose_succ,stock_succ]
     have h₀:=mul_nonneg hv (zero_le_one.trans (dose_one A P m k))
     intro i a s
     apply (curl_varied_eq M P hp heq N (m+k) p (by omega) (div_nonneg h₀ (by exact pow_nonneg (by exact (stock_pos ..).le) _ : 0≤ (stock A m k)^3)) _ hk' i a s).trans_eq; ring_nf
end horizon
end YM.Extension.UV.Linear
