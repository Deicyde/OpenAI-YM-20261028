import YM.Pert.Bulk.Crossing

set_option autoImplicit false
noncomputable section
namespace YM.Pert.Bulk
open Lattice Stationary Laurent RG
open scoped ENNReal Topology BigOperators Classical
variable {X Y Z α β γ : Type} {L:Side}

def tagged (K : Kernel α β) (D : Kernel β γ) (j : β) (x : Market α) (y: Market γ) := ∑'z, K x (z,j) * D (z,j) y
def bind [Fintype β] (K : Kernel α β) (D : Kernel β γ) : Kernel α γ := ∑ j,tagged K D j
lemma bind_apply [Fintype β] (K : Kernel α β) (D : Kernel β γ) x y : bind K D x y=∑ j,tagged K D j x y := by simp [bind]

def bill_tsum (f: X→ℝ) t : bill (∑'x,f x) t ≤ ∑'x,bill (f x) t := by
  have h z : bill z t = ‖z‖ₑ * ENNReal.ofReal (Real.exp t) := by rw [bill_eq,← ofReal_norm_eq_enorm,Real.norm_eq_abs]
  simp_rw [h,ENNReal.tsum_mul_right]; exact mul_le_mul_left enorm_tsum_le_tsum_enorm _
lemma bill_sum {s:Finset X} (f:X→ℝ) t : bill (∑x∈s,f x) t ≤ ∑x∈s,bill (f x) t := by
  simp_rw [bill_eq,← Finset.sum_mul]; apply mul_le_mul_left; rw [← ENNReal.ofReal_sum_of_nonneg (s:=s) (f:=fun i=>|f i|) ?_ ]
  · exact ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)
  exact fun i _ => abs_nonneg _

lemma bill_mul (x y s t z : ℝ) (h:t≤s+z) : bill (x*y) t ≤ bill x s * bill y z := by
  simp only [bill_eq, ← ENNReal.ofReal_mul (abs_nonneg (x*y)),← ENNReal.ofReal_mul (abs_nonneg x),← ENNReal.ofReal_mul (abs_nonneg y), ← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg x) (Real.exp_pos _).le)]
  apply ENNReal.ofReal_le_ofReal
  rw [abs_mul,mul_mul_mul_comm, ← Real.exp_add]; gcongr

lemma rowBind {K : Kernel α β} {j:β} {D : Kernel β γ} {p q:ℝ} (hp:0≤p)(hq:0≤q)
    {bK:Market α→Market β→ℝ} {bD:Market β→Market γ→ℝ}
    (hk:∀ v j,∑'z,bill (K v (z,j)) (bK v (z,j))≤ENNReal.ofReal p)
    (hd:∀ u k,∑'y,bill (D u (y,k)) (bD u (y,k))≤ENNReal.ofReal q)
    {bM:Market α→Market γ→ℝ}
    (h : ∀ v u w, bM v w ≤ bK v u + bD u w) (x:Market α)(k:γ) :
    ∑'y,bill (tagged K D j x (y,k)) (bM x (y,k)) ≤ ENNReal.ofReal (p*q) := by
  calc
    _ ≤ (∑' y, ∑' z,bill (K x (z,j)) (bK x (z,j)) * bill (D (z,j) (y,k)) (bD (z,j) (y,k))) := by
      refine ENNReal.tsum_le_tsum fun y => (bill_tsum ..).trans (ENNReal.tsum_le_tsum fun z=> bill_mul _ _ _ _ _ (h ..))
    _ = ∑' z,bill (K x (z,j)) (bK x (z,j)) * ∑' y,bill (D (z,j) (y,k)) (bD (z,j) (y,k)) := by rw [ENNReal.tsum_comm]; simp_rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' z,bill (K x (z,j)) (bK x (z,j)) * ENNReal.ofReal q := ENNReal.tsum_le_tsum (fun z => mul_le_mul_right (hd ..) _)
    _ ≤ _ := by rw [ENNReal.tsum_mul_right,ENNReal.ofReal_mul hp]; exact mul_le_mul_left (hk ..) _
lemma colBind {K : Kernel α β} {D : Kernel β γ} {j:β} {p q:ℝ} (hp:0≤p)(hq:0≤q)
    {bK:Market α→Market β→ℝ} {bD:Market β→Market γ→ℝ}
    (hk:∀ v i,∑'z,bill (K (z,i) v) (bK (z,i) v)≤ENNReal.ofReal p)
    (hd:∀ u k,∑'y,bill (D (y,k) u) (bD (y,k) u)≤ENNReal.ofReal q)
    {bM:Market α→Market γ→ℝ}
    (h : ∀ v u w, bM v w ≤ bK v u + bD u w) (x:Market γ)(k:α) :
    ∑'y,bill (tagged K D j (y,k) x) (bM (y,k) x) ≤ ENNReal.ofReal (p*q) := by
  calc
    _ = ∑'y,bill (tagged (Function.swap D) (Function.swap K) j x (y,k)) (bM (y,k) x) := by simp [tagged,mul_comm,Function.swap]
    _ ≤ ENNReal.ofReal (q*p) := @rowBind γ β α (Function.swap D) j (Function.swap K) q p hq hp
     (Function.swap bD) (Function.swap bK) hd hk (Function.swap bM) (by intro v u w; change _ ≤ _; rw [add_comm]; exact h ..) x k
    _ = _ := by rw [mul_comm]

lemma full_sum [Fintype X] (a:X→Y→ℝ≥0∞) (p:ℝ) (hp:0≤p) (ha:∀ x,∑'y,a x y ≤ ENNReal.ofReal p) : ∑'y,∑ x,a x y ≤ ENNReal.ofReal (Fintype.card X * p) := by
  have hz (y:Y) : ∑ x,a x y = ∑' x,a x y := by rw [tsum_fintype]
  simp_rw [hz,ENNReal.tsum_comm (f:=fun y x=>a x y),tsum_fintype]
  calc ∑ _,_ ≤ ∑ _ : X, ENNReal.ofReal p := Finset.sum_le_sum fun _ _ => ha _
       _ = _ := by simp [nsmul_eq_mul,ENNReal.ofReal_mul (by positivity : (0:ℝ)≤Fintype.card X)]

lemma row_block [Fintype β] {K : Kernel α β} {D : Kernel β γ} {σ θ r p q:ℝ} (hp:0≤p)(hq:0≤q) {L' L'' : Side}
    (hk:RowCost σ L K p) (hd:RowCost r L' D q) (h:∀ x y z, θ*delta L'' x z≤σ*delta L x y+r*delta L' y z) : RowCost θ L'' (bind K D) (Fintype.card β * (p*q)) := by
     intro v u; simp_rw [bind_apply]
     apply (ENNReal.tsum_le_tsum fun y => bill_sum ..).trans (full_sum (p:=p*q) _ (mul_nonneg hp hq) ?_)
     intro j; exact rowBind (bK:=fun v u=>σ*delta L v.1 u.1) (bD:=fun v u=>r*delta L' v.1 u.1) (bM:=fun v u=>θ * delta L'' v.1 u.1) (j:=j) (K:=K) (D:=D) hp hq hk hd (fun v u w => h ..) v u
lemma col_block [Fintype β] {K : Kernel α β} {D : Kernel β γ} {σ θ r p q:ℝ} (hp:0≤p)(hq:0≤q) {L' L'' : Side}
    (hk:ColCost σ L K p) (hd:ColCost r L' D q) (h:∀ x y z, θ*delta L'' x z≤σ*delta L x y+r*delta L' y z) : ColCost θ L'' (bind K D) (Fintype.card β * (p*q)) := by
     intro u v; simp_rw [bind_apply]
     apply (ENNReal.tsum_le_tsum fun y => bill_sum ..).trans (full_sum (p:=p*q) _ (mul_nonneg hp hq) ?_)
     intro j; exact colBind (bK:=fun v u=>σ*delta L v.1 u.1) (bD:=fun v u=>r*delta L' v.1 u.1) (bM:=fun v u=>θ * delta L'' v.1 u.1) (j:=j) (K:=K) (D:=D) hp hq (fun v u=>hk u v) (fun v u=>hd u v) (fun v u w => h ..) v u
end YM.Pert.Bulk
