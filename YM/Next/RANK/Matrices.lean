import YM.Next.RANK.Tuning
import YM.Work.G08


/-!
# Finite normalization tests and inverse budgets

Use the actual primary coordinates, linear *perturbation* input (which must
be supplied e.g. by kpc plus its power-of-p gate uniformly from the same
comparison as the marker estimates; not claiming to derive Wick readout
here). We check there really is an exact solution in reference coordinates
on the original family at each such k,N,p. Scale to unnormalized k units
*before* solving; this also gives a useful bound uniform through N and p at
each k.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Price
open Function Set Filter Complex RG Lattice Wilson Cells MeasureTheory Station Work.G08
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators ENNReal

variable {G : Gauge} (C : Family G) {d N p k : ℕ}

-- origin x records on terminal reference vector (not its norm or IR representative).

def columns (D k N p : ℕ) (v : C.label D) : C.label D :=
    let T := C.factory D N p
    (T.entries k (T.terminal.symm v)).x

def awake (D k N p : ℕ) (v : C.label D) := ((C.S.a k:ℂ)^D)⁻¹ • columns C D k N p v



private lemma size_sc {P : Labels.Frame G d} (g : P.Coeff) (x : ℂ) : P.coeffSize (x • g)=‖x‖*P.coeffSize g := by
  unfold Labels.Frame.coeffSize; simp only [Pi.smul_apply,norm_smul,Finset.mul_sum]

-- This front cost only paid at fixed k (not raised repeatedly in the endpoint estimate).
def outward (d k : ℕ) := ∏ i∈ Finset.range k, (C.path.levels.params (i+1)).columns*((C.S.block i).val : ℝ)^d
lemma outward_nn (d k : ℕ) : 1 ≤ outward C d k := Finset.one_le_prod fun i _ => one_le_mul_of_one_le_of_one_le
    (C.path.levels.params (i+1)).columns_ge (one_le_pow₀ (by exact_mod_cast (C.S.block i).property))

lemma at_current (h : C.Makes) (hk : C.ref d ≤ k) (hn : k ≤ N) (p : ℕ) (v : C.book.Ref d) :
    (C.labels.level d).coeffSize v ≤ outward C d k * (C.labels.level d).coeffSize (columns C d k N p v) := by
  let Z := C.labels.level d
  induction k,hk using Nat.le_induction with
  | base =>
    rw [show columns C d (C.ref d) N p v=v from C.normalized h hn v]
    exact le_mul_of_one_le_left (size_nonneg _ _) (outward_nn ..)
  | succ i hi ih =>
    apply (ih (by omega)).trans
    let Y := C.factory d N p
    have hy : Y.Based _ _ _ := h.calibrated _ N p (by omega)
    have hx := hy.front i hi hn (Y.terminal.symm v)
    apply (mul_le_mul_of_nonneg_left hx (zero_le_one.trans (outward_nn C d i))).trans_eq
    unfold outward; rw [Finset.prod_range_succ]
    rw [← mul_assoc];rfl

lemma reference_size (h : C.Makes) (hk : C.ref d ≤ k) (hn : k ≤ N) (p : ℕ) (v : C.book.Ref d) :
    (C.labels.level d).coeffSize v ≤ outward C d k * (C.S.a k)^d * (C.labels.level d).coeffSize (awake C d k N p v) := by
  have he := C.S.a_pos k
  apply (at_current _ h hk hn p v).trans_eq; rw [awake,size_sc,norm_inv,norm_pow,Complex.norm_real, Real.norm_of_nonneg he.le]; field_simp

/-- kpc-style estimate. `read` on *reference* coeffs, calibrated on the origin
primary. Values here include `t_k` weights before resetting by g/t. Need such
maps together with the mixed-source receipt, not just existence of some map
with a cheap norm. Score demand intentionally at ℓ¹ in the frame. -/
structure Tested (d k N p : ℕ) (read : C.label d →ₗ[ℂ] C.label d) : Prop where
  unit : read (C.refUnit d) = (C.labels.level d).e0
  preserves v : read (star v) = star (read v)
  score v :
    let F := C.labels.level d; let a := awake C d k N p v
    F.coeffSize (a-read v) ≤ F.coeffSize a/2

lemma Tested.cost (read : C.label d →ₗ[ℂ] C.label d) (c : Tested C d k N p read) (v : C.label d) :
    (C.labels.level d).coeffSize (awake C d k N p v) ≤ 2*(C.labels.level d).coeffSize (read v) := by
  have he := size_triangle (C.labels.level d) (awake C d k N p v) (read v); linarith only [he,c.score v]

lemma Tested.bijective (h : C.Makes) (hk : C.ref d ≤ k) (hn : k ≤ N) (read : C.label d →ₗ[ℂ] C.label d) (c : Tested C d k N p read) :
    Bijective read := by
  have he : Injective read := by
    apply LinearMap.ker_eq_bot.mp; apply LinearMap.ker_eq_bot'.mpr
    intro v hv; apply size_separates (C.labels.level d)
    have hx := c.cost _ _ v; rw [hv, show (C.labels.level d).coeffSize 0=0 by simp [Labels.Frame.coeffSize],mul_zero] at hx
    apply le_trans (reference_size _ h hk hn p v)
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (zero_le_one.trans (outward_nn ..)) (pow_nonneg (C.S.a_pos _).le _)) hx
  exact ⟨he,LinearMap.surjective_of_injective he⟩

/-- Apply *position* bidegree weight separately (vs factor power in `Frame.scaled`). -/
def weightTag (d : ℕ) (ρ : ℝ) : C.label d →ₗ[ℂ] C.label d where
  toFun v i := ((ρ:ℂ)^(C.labels.level d|>.grades i).1)*v i
  map_add' x y := by funext i; rw [Pi.add_apply,mul_add];rfl
  map_smul' x y := by funext i; simp;ring

lemma weight_tag_zero (d : ℕ) (ρ : ℝ) : weightTag C d ρ (C.labels.level d).e0 = (C.labels.level d).e0 := by
  ext i; by_cases h : i=0
  · subst i; simp [weightTag,Labels.Frame.zero_degree]
  simp [weightTag,Labels.Frame.e0,h]

lemma weight_tag_real (d : ℕ) (ρ : ℝ) (x : C.label d) : weightTag C d ρ (star x)=star (weightTag C d ρ x) := by
  ext1 i; simp [weightTag]

-- g_k/t_k at level k, original barrier, not the restarted one.

def shrink (k N p : ℕ) := (Real.sqrt (C.path.β N p k))⁻¹ / C.path.levels.clock.threshold k

lemma shrink_pos (h : C.Makes) (hk : k≤N) (p : ℕ) : 0<shrink C k N p :=
    div_pos (inv_pos.mpr (Real.sqrt_pos.2 (Overlay.beta_positive h.wilson hk))) (C.path.levels.budget k).threshold_pos

lemma shrink_min (h : C.Makes) (hk : k≤N) (p : ℕ) : (shrink C k N p)⁻¹ ≤ 2*C.path.levels.clock.monitor k := by
  let A := C.path.levels.clock; let B := A.hatBeta k; let t:= A.threshold k
  have he : 0<t := (C.path.levels.budget k).threshold_pos
  have hx : 0<B := lt_trans zero_lt_one (C.path.levels.fits.delayed k)
  have hp : 0 < C.path.β N p k := Overlay.beta_positive h.wilson hk
  have hc : C.path.β N p k ≤ 2*B := (h.wilson.represents N p k hk).band.2
  calc
    _ = t * Real.sqrt (C.path.β N p k) := by unfold shrink; simp only [inv_div,div_inv_eq_mul];rfl
    _ ≤ t * (2 * Real.sqrt B) := by
      apply mul_le_mul_of_nonneg_left _ he.le
      nlinarith [Real.sqrt_nonneg B,Real.sq_sqrt hp.le,Real.sq_sqrt hx.le]
    _ = _ := by
      change ((Real.sqrt B)⁻¹ * (A.monitor k)) * _ = 2 * A.monitor k
      have he := Real.sqrt_pos.2 hx; field_simp

/-- The exact solving condition, not a comparison drift of the target labels
in k-units. -/
def Solves (ρ : ℝ) (d k N p : ℕ) (T : C.label d →ₗ[ℂ] C.label d) (basis v : C.label d) :=
  (C.labels.level d).scaled (shrink C k N p) (T v)=weightTag C d ρ basis

lemma solve (h : C.Makes) (hk : C.ref d ≤ k) (hn : k≤N) {read : C.label d →ₗ[ℂ] C.label d}
    (c : Tested C d k N p read) (v : C.label d) (ρ : ℝ) : ∃! u : C.label d, Solves C ρ d k N p read v u := by
  let Y := C.labels.level d; let a := weightTag C d ρ v
  have hr := Tested.bijective C h hk hn _ c
  let t := shrink C k N p
  have ht : 0<t := shrink_pos C h hn p
  obtain ⟨w,hw⟩ := hr.2 (Y.scaled t⁻¹ a)
  refine ⟨w,?_,?_⟩
  · change Y.scaled t (read w)=a; rw [hw,Y.scaled_inv ht.ne']
  intro y hy
  apply hr.1; rw [hw, ← show Y.scaled t (read y)=a from hy]
  have he := Y.scaled_inv (inv_ne_zero ht.ne') (read y); rw [inv_inv] at he; exact he.symm

-- choose a coherent basis representative (one for the whole sequence).

structure Representatives {S : Table C.book} {d : ℕ} (X : Columns C S d) where
  rep : Fin (X.dim+1) → C.label d
  real i : star (rep i) = rep i
  projection i : (standard C).project d (rep i) = X.basis i
  start : rep 0=(C.labels.level d).e0

variable {S : Table C.book}

lemma from_labels (X : Columns C S d) : Nonempty (Representatives C X) := by
  let F:= standard C
  choose a hx hy hz using fun i : Fin (X.dim+1) => show ∃ c : C.label d,
      star c=c ∧ F.project d c=X.basis i ∧ (i=0→ c=(C.labels.level d).e0) from by
    by_cases hi : i=0
    · subst i
      have hv : (Maxwell.standard C.labels).scalar d=(C.labels.level d).e0 := by
        unfold Register.scalar Maxwell.standard Register.coord; simp [← Labels.Frame.coords_unit]
      refine ⟨_,?_,?_,fun _ => hv⟩
      · exact (Maxwell.standard C.labels).bar_scalar _
      rw [X.initial];rfl
    obtain ⟨y,h⟩ := F.onto d (X.basis i)
    let p := ((2:ℂ)⁻¹) • (y+star y)
    refine ⟨p,?_, ?_,fun h => (hi h).elim⟩
    · ext1 i; change star (p i)=p i; simp [p, add_comm]
    unfold p; rw [map_smul,map_add, ← F.conj_project X.H d y,h,X.realBasis]
    rw [← two_smul ℂ, smul_smul, inv_mul_cancel₀ (by norm_num),one_smul]
  exact ⟨⟨a,hx,hy,hz 0 rfl⟩⟩

variable {X : Columns C S d} (p' : Representatives C X) (ρ : ℝ)

def Names (k N p : ℕ) (T : C.label d→ₗ[ℂ] C.label d) (x : Fin (X.dim+1) → C.label d) :=
  ∀ i, Solves C ρ d k N p T (p'.rep i) (x i)

lemma series (h : C.Makes) (hk : C.ref d ≤ k) (hn : k≤N) {T : C.label d →ₗ[ℂ] C.label d}
    (c : Tested C d k N p T) : ∃ x, Names C p' ρ k N p T x ∧ x 0=C.refUnit d ∧ ∀ i, star (x i)=x i := by
  choose x H ht using fun i => solve C h hk hn c (p'.rep i) ρ
  refine ⟨x,H, Eq.symm (ht 0 _ ?_), fun i => ht i (star (x i)) ?_⟩
  · dsimp only [Solves]; rw [p'.start, c.unit,weight_tag_zero, Labels.Frame.scaled_unit]
  have he (j : ℝ) (s : C.label d) : (C.labels.level d).scaled j (star s)=star ((C.labels.level d).scaled j s) := by ext1 i; simp
  dsimp only [Solves]; rw [c.preserves,he,H i,← weight_tag_real,p'.real]

/-- At each fixed k, the solutions stay inside a common bound independent
of cutoff and period. Importantly this doesn't need a kernel estimate
beyond `c.Tested` and h. -/
lemma within (h : C.Makes) (hk : C.ref d≤k) : ∃ A : ℝ, ∀ N, k ≤ N → ∀ p T,
    Tested C d k N p T → ∀ x, Names C p' ρ k N p T x → ∀ i, ‖x i‖≤A := by
  let Z := C.labels.level d
  let F (i : Fin (X.dim+1)) := weightTag C d ρ (p'.rep i)
  let r := 2*C.path.levels.clock.monitor k
  let B i := Z.coeffSize (Z.scaled r (F i))
  refine ⟨outward C d k * (C.S.a k)^d * (2*∑ i,B i),fun N hN p T ht x hx i => ?_⟩
  let a := shrink C k N p
  have h₁ : 0<a := shrink_pos C h hN p
  have h₂ : a⁻¹≤r := shrink_min C h hN p
  have hp : T (x i)= Z.scaled a⁻¹ (F i) := by
    have hv := Z.scaled_inv (inv_ne_zero h₁.ne') (T (x i)); rw [inv_inv,hx i] at hv; exact hv.symm
  have he : Z.coeffSize (T (x i)) ≤ B i := by
    rw [hp]; unfold B Labels.Frame.coeffSize
    refine Finset.sum_le_sum fun j _ => ?_
    have h₀ : 0 < r := lt_of_lt_of_le (inv_pos.mpr h₁) h₂
    simp only [Labels.Frame.scaled_apply,norm_mul,norm_real]
    rw [Real.norm_of_nonneg (pow_nonneg (inv_pos.mpr h₁).le _), Real.norm_of_nonneg (pow_nonneg h₀.le _)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (inv_pos.mpr h₁).le h₂ _) (norm_nonneg _)
  apply (show ‖x i‖ ≤ Z.coeffSize (x i) from ?_).trans
  · apply (reference_size C h hk hN p (x i)).trans
    exact mul_le_mul_of_nonneg_left ((ht.cost _ _ _).trans (mul_le_mul_of_nonneg_left
      (he.trans (Finset.single_le_sum (fun i _ => show 0 ≤ B i from size_nonneg Z _) (Finset.mem_univ i))) (by norm_num)))
      (mul_nonneg (zero_le_one.trans (outward_nn ..)) (pow_nonneg (C.S.a_pos _).le _))
  apply (pi_norm_le_iff_of_nonneg (size_nonneg Z (x i))).2
  exact fun j => Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
end YM.Next.Rank.Price
