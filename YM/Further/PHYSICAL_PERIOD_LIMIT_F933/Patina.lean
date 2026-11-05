import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Paintings

/-!
# Taking the TRUE period limit on rational grids

No θ-spectrum or imaginary interpolant. Can always ask post-L
because callers in Step/T.kin preserve Path recipe across periods;
do NOT retune R.Kin after changing the horizon. Inactive mesh sizes c
can use only comparison from large qualifying sizes. The S.loans supplied
later actually do cover all native arguments, not every theoretical extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Paintings.Supply
open Gauge Filter Jacobi Macrame Macrame.Lace Polytrace Withdrawal Liquid Enamel Loom Function Lattice RG Tree Matrix Finset Precision Exterior Bid Wilson Set Metric Push.Uniform Push Shingle Pitch Extra.Iteration Extra.Iteration.Calibration
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {P : Patch} {Q : KernelChoices} {T : Stage} (A : Paintings.Supply G P Q T) {c C f : Side}
  {R : PathData G} {Λ : ℝ} (hp : R.Bounds T.clip T.width T.paths Λ) {O : ChartRatio G}

theorem h0 (c : Side) (P : Patch) : (canvas P c).val=c.val*P.L.val := rfl
def serves (c : Side) := A.bulletin (h0 c P) -- h0 insert

def buys (O : ChartRatio G) (x y : Paintings.scale c G) := if h : A.serves c then A.billing (h0 c P) h R hp O x y else 0

def replicate (h : c.val ∣ C.val) : Paintings.scale c G →L[ℝ] Paintings.scale C G :=
    onpass (fun j : Primary C G=> (((splitter h j.1.1,j.1.2):Body 1 c),j.2))
lemma compose {d : Side} (h : c.val∣ C.val) (hD : C.val∣d.val) (x : Paintings.scale c G) :
    replicate hD (replicate h x)=replicate (h.trans hD) x := by
  funext j; change x ((splitter h (splitter hD j.1.1),_),_) = x ((splitter (h.trans hD) j.1.1,_),_)
  congr 3
  obtain ⟨u, hu⟩ : ∃ u:Cover, wrap d u=j.1.1 := ⟨_,wrap_lift ..⟩
  rw [← hu,branch,branch,branch]


lemma honest (hb : A.serves c) {h : f.val=c.val*P.L.val} (H : A.bulletin h) (O : ChartRatio G) (x y : Paintings.scale c G) :
    A.billing h H R hp O x y=A.buys hp O x y := by
  unfold buys; rw [dif_pos hb]
  have he : f=canvas P c := Subtype.ext h
  subst f; rfl
lemma rows (hb : A.serves c) : 2 ≤ c.val := hb.2.2
lemma mounts {n : ℕ} (hC : C.val=c.val*n) (hc : A.serves c) : A.serves C := by
  have h : c.val ≤ C.val := hC ▸ Nat.le_mul_of_pos_right _ (Nat.pos_of_mul_pos_left (show 0<c.val*n from hC ▸ C.property))
  exact ⟨A.larger,show 100*Pressure.macroR P ≤ C.val*P.L.val from hc.2.1.trans (Nat.mul_le_mul_right _ h),hc.2.2.trans_le h⟩

abbrev price (c : Side) := A.allowance * Real.exp (-A.sights*(c.val:ℝ))
include hp
lemma sight (ho : LocalRatio O) {n : ℕ} (hC : C.val=c.val*n) (hc : A.serves c) (x y : Paintings.scale c G) (hx : ‖x‖ ≤ 1) (hy : ‖y‖≤1) :
    let l := replicate (show c.val ∣ C.val from ⟨n,hC⟩)
    0<A.sights ∧ 0≤A.allowance ∧ |A.buys hp O x y-A.buys hp O (l x) (l y)| ≤ A.price c := by
  intro l
  unfold buys; rw [dif_pos hc, dif_pos (A.mounts hC hc)]; exact move A hp ho hC (A.rows hc) hc (A.mounts hC hc) x y hx hy

local notation "ρ" => Paintings.scale c G
def stretch (c : Side) (n : ℕ) : Side := ⟨c.val*(n+1),Nat.mul_pos c.property (Nat.succ_pos _)⟩
omit hp in
lemma view (c : Side) (n : ℕ) : c.val∣(stretch c n).val := ⟨n+1,rfl⟩

def extendsAt (O : ChartRatio G) (x y : ρ) (n : ℕ) :=
  A.buys hp O (replicate (view c n) x) (replicate (view c n) y)

variable (ho : LocalRatio O)
include ho hp
lemma chalk (hb : A.serves c) (x y : ρ) (hx : ‖x‖≤1) (hy : ‖y‖≤1) (i j : ℕ) :
    |A.extendsAt hp O x y i-A.extendsAt hp O x y j| ≤ A.price (stretch c i)+A.price (stretch c j) := by
  let N i := stretch c i
  let C : Side := stretch (stretch c i) j
  have hi : C.val = (N i).val*(j+1) := rfl
  have he : C.val = (N j).val*(i+1) := by change _ = c.val*(j+1)*(i+1); change c.val*(i+1)*(j+1)=_; ring
  let V i (x:ρ) := replicate (view c i) x
  have hv i (x) (hx : ‖x‖≤1) : ‖V i x‖≤1 := (Pitch.pressure _ x).trans hx
  let p : c.val∣ C.val := (view c i).trans ⟨_,hi⟩
  let z:=A.buys hp O (replicate p x) (replicate p y)
  apply (abs_sub_le (A.extendsAt hp O x y i) z (A.extendsAt hp O x y j)).trans
  suffices h : ∀ (s v : ℕ), C.val=(N s).val*v → |A.extendsAt hp O x y s - z| ≤ A.price (N s) by
    rw [abs_sub_comm z]; exact add_le_add (h i _ hi) (h j _ he)
  intro s v hs
  have hh := (A.sight hp ho hs (A.mounts (C:=N s) (n:=s+1) rfl hb) (V s x) (V s y) (hv s x hx) (hv s y hy)).2.2
  dsimp only [extendsAt,V] at *
  rw [compose,compose] at hh; exact hh

lemma toZero (hb : A.serves c) : Tendsto (fun n=>A.price (stretch c n)) atTop (𝓝 0) := by
  have ht := A.sight hp ho (c:=c) (C:=c) (n:=1) (mul_one _).symm hb (0:ρ) 0 (by simp) (by simp)
  have he : Tendsto (fun m:ℕ=>(↑((stretch c m).val):ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun i=>show i≤(stretch c i).val from i.le_succ.trans (Nat.le_mul_of_pos_left _ c.property)) tendsto_id)
  have hx := (Real.tendsto_exp_neg_atTop_nhds_zero.comp (he.const_mul_atTop ht.1)).const_mul A.allowance
  simpa only [mul_zero,Function.comp_def,price,neg_mul] using hx
lemma coherent (hb : A.serves c) (x y : ρ) (hx : ‖x‖≤1) (hy : ‖y‖≤1) :
    ∃ z : ℝ, Tendsto (A.extendsAt hp O x y) atTop (𝓝 z) := by
  apply cauchySeq_tendsto_of_complete; rw [Metric.cauchySeq_iff]; intro t hT
  obtain ⟨j,hj⟩:= Filter.eventually_atTop.1 ((A.toZero hp ho hb).eventually (gt_mem_nhds (half_pos hT)))
  refine ⟨j,fun i hi k hk=>?_⟩
  rw [Real.dist_eq]; have hb := A.chalk hp ho hb x y hx hy i k
  have hj i (hi : j ≤ i) : A.price (stretch c i) < t/2 := hj _ hi
  linarith [hj i hi,hj k hk]

/-- Actually converges. Totalize fake inputs but not pay them. -/
def limit (O : ChartRatio G) (x y : ρ) :=
  if h:∃ z:ℝ, Tendsto (A.extendsAt hp O x y) atTop (𝓝 z) then h.choose else 0
lemma stability (hb : A.serves c) (x y : ρ) (hx : ‖x‖≤1) (hy : ‖y‖≤1) :
    Tendsto (A.extendsAt hp O x y) atTop (𝓝 (A.limit hp O x y)) := by unfold limit; rw [dif_pos (A.coherent hp ho hb x y hx hy)]; exact Exists.choose_spec (A.coherent hp ho hb x y hx hy)

lemma spent (hb : A.serves c) (x y : ρ) (hx : ‖x‖≤1) (hy : ‖y‖≤1) :
    0<A.sights ∧ 0≤A.allowance ∧
    |A.buys hp O x y-A.limit hp O x y| ≤ A.price c := by
  have hs i := A.sight hp ho (C:=stretch c i) (n:=i+1) rfl hb x y hx hy
  let Y:= A.buys hp O x y
  have hh : Tendsto (fun i : ℕ=>|Y-A.extendsAt hp O x y i|) atTop (𝓝 (|Y-A.limit hp O x y|)) := Filter.Tendsto.abs (tendsto_const_nhds.sub (A.stability hp ho hb x y hx hy))
  exact ⟨(hs 0).1,(hs 0).2.1,le_of_tendsto_of_tendsto hh tendsto_const_nhds (Filter.Eventually.of_forall (fun i=>(hs i).2.2))⟩


end YM.Further.PhysicalPeriodLimitF933.Paintings.Supply
