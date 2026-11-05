import YM.Next.RANK.Bird
import YM.Next.RANK.BoundParticle


/-!
# Deriving rates for the Maxwell approximation

Pre-L powers here: b, K(degree), D(jets), E (original cost).
J and L dependent costs must use only crumbs in comparison gates (p^fuel),
need these actual estimates at every stamp. Numeric feasibility does not instantiate.
Includes uniform free-table use (on aligned normalized points), even arbitrary arity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Glimmer
open Function Set Filter RG Lattice Wilson Cells Read Value  Perch Particle Common Rise Normal Configuration Glyph Exponential Marker Labels
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {P : Levels G} {x : ℝ}

def fuel (k n : ℕ) := 1/(4*((n*k:ℕ)+ k +1:ℝ))
lemma fuel_real (k n : ℕ) : 0 < fuel k n := by unfold fuel; positivity
lemma fuel_food (n k) : fuel k n*(n*k:ℕ) ≤ 1/4 := by
  unfold fuel; rw [div_mul_eq_mul_div]; refine (div_le_iff₀ (by positivity)).2 ?_
  push_cast; linarith
lemma fueled (n k) : fuel k n*k ≤ 1/4 := by
  unfold fuel; rw [div_mul_eq_mul_div]; refine (div_le_iff₀ (by positivity)).2 ?_; push_cast; nlinarith

lemma bills (a s : ℝ) (k : ℕ) : bill a s ^ k=bill (a*k) s := by unfold bill; rw [← Real.exp_nat_mul]; congr 1; ring
lemma costed (a s : ℝ) (ha : 0≤a) : 1 ≤ bill a s := Real.one_le_exp (mul_nonneg (boil_pos _) ha)
lemma billed (s : ℝ) {a b : ℝ} (h : a≤b) : bill a s ≤ bill b s := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h (boil_pos _))
lemma bill_zero (s : ℝ) : bill 0 s=1 := by simp [bill]

lemma transports {a b : ℝ} (h : a<b) (c : ℝ) : ∀ᶠ s in atTop, c*bill a s ≤ bill b s := by
  filter_upwards [(bill_lo (show 0 < b-a by linarith)).eventually_ge_atTop c] with s hs
  rw [show b=(b-a)+a by ring, ← overlap]; exact mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le

-- Degree orders may have to exceed b*n: only in denominator in fuel.
lemma collected (n k : ℕ) (A : ℝ) (ha : 1≤A) : ∀ᶠ s in atTop,
    (n:ℝ)*bill (-2) s*(A+bill (-2) s)^n*priced (bill (fuel k n) s) (n*k)+A^n*(bill (-2) s * priced (bill (fuel k n) s) (n*k)) ≤ bill (-3/2) s := by
  let a := fuel k n
  let d := n*k
  let b := (2*((d:ℝ)+1))^d
  let f (s : ℝ) := priced (bill a s) d
  have hp s : f s ≤ b*bill (1/4) s := by
    unfold f priced
    rw [show 2*bill a s*(↑d+1)= (2*((d:ℝ)+1))*bill a s by ring, mul_pow, bills]
    exact mul_le_mul_of_nonneg_left (billed s (fuel_food n k)) (by positivity)
  let c := n*(A+1)^n*b+A^n*b
  filter_upwards [transports (show (-2:ℝ)+1/4 < -3/2 by norm_num) c] with s hs
  apply le_trans _ hs
  rw [← overlap]; let g := bill (-2) s
  let r := bill (1/4) s
  have hw : g ≤ 1 := (billed s (show (-2:ℝ)≤0 by norm_num)).trans (bill_zero s).le
  have ht : 0 ≤ b := by unfold b; positivity
  have hb := zero_lt_one.trans_le ha; have hv : 0≤g := (Real.exp_pos _).le; have hr : 0 ≤ r := (Real.exp_pos _).le
  change (n:ℝ)*g*(A+g)^n*f s+A^n*(g*f s) ≤ _
  have hf : 0 ≤ f s := by dsimp only [f,priced,bill]; positivity
  have he := mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0≤A+g by linarith) (add_le_add_right hw A) n)
    (show 0≤(n:ℝ)*g by positivity)) (hp s) hf (by positivity)
  apply (add_le_add he (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hp s) hv) (pow_nonneg hb.le _))).trans_eq
  change _=c*(g*r); dsimp only [c,g,f,r]; ring

variable {A V : Type*}

def costs (n k : ℕ) (a s : ℝ) := ∃ P : Spend n k,
    P.ξ=bill (-2) s ∧ P.base=a ∧ P.collision=bill (-2) s ∧ P.B=bill (fuel k n) s ∧ P.cost=bill (-3/2) s
lemma shed (n k : ℕ) (a : ℝ) (ha : 1≤a) : ∀ᶠ s in atTop,costs n k a s :=
  (collected n k a ha).mono fun _ hs => ⟨⟨_,_,(Real.exp_pos _).le,ha,_,_,_,hs⟩,rfl,rfl,rfl,rfl,rfl⟩

lemma ticket (k n d : ℕ) (E b : ℝ) (h : E+3 ≤ b) (s : ℝ) : bill (b*d+E) s * bill (fuel k n) s ^ k ≤ bill (-2) s*bill b s ^ (d+1) := by
  rw [bills,bills,overlap,overlap]; apply billed; push_cast; nlinarith only [fueled n k,h]

-- smooth logarithm (also has explicit Price version, use only fixed n).
variable [DecidableEq V] [Fintype V]
private lemma pass_smooth : ContDiff ℂ 1 (@Poly.pass V _ (Stock.census V) _) := by
  have he (i : modes V) (k : ℕ) : ContDiff ℂ 1 (fun x : veil V => (x^k).part i) := by
    induction k generalizing i with
    | zero => simp only [pow_zero]; exact contDiff_const
    | succ k H =>
      simp_rw [pow_succ,Glyph.part_mul]; exact ContDiff.sum (fun j _ => (H (scene j)).mul (Poly.get _).contDiff)
  change ContDiff ℂ 1 (fun x => (Poly.pass x).part)
  apply contDiff_pi.mpr; intro i
  simp only [Poly.pass,Poly.part_sum, Poly.part_smul]; exact ContDiff.sum (fun j _ => contDiff_const.mul (he i j))
private lemma rolling (k : ℕ) : ContDiff ℂ 1 (fun p : veil V => roll p k) := by
  induction k with
  | zero => exact contDiff_const
  | succ k H => exact H.add (contDiff_id.sub (@pass_smooth V _ _|>.comp H))

lemma accumulate (α : Type*) (l : Filter α) (f : α → veil V) (p : veil V) (h : Tendsto f l (𝓝 p)) (s : α → ℝ) (hs : Tendsto s l atTop) :
    ∀ᶠ i in l, ∀ q Q Q', Expands Q q → Expands Q' (f i) → (∀ k, ‖q.part k-(f i).part k‖ ≤ bill (-3/2) (s i)) →
      ‖Q-Q'‖ + bill (-3/2) (s i) ≤ bill (-31/32) (s i) := by
  let n := Fintype.card V; let F := fun t : veil V => roll t n
  obtain ⟨A,H,x,hF⟩ := (show ContDiffAt ℂ 1 F p from (rolling n).contDiffAt).exists_lipschitzOnWith
  obtain ⟨ε,hε,hp⟩ := Metric.mem_nhds_iff.mp x
  filter_upwards [hs.eventually (transports (show (-3:ℝ)/2 < -31/32 by norm_num) (A+1)),
    h.eventually (Metric.ball_mem_nhds p (half_pos hε)),
    ((bill_hi (show (-3:ℝ)/2<0 by norm_num)).comp hs).eventually (ge_mem_nhds (half_pos hε))] with i h₁ h₂ h₃ q Q Q' Hq Hq' hy
  have he : ‖q-f i‖ ≤ bill (-3/2) (s i) := by change ‖q.part - (f i).part‖ ≤ _; exact (pi_norm_le_iff_of_nonneg (by exact (Real.exp_pos _).le)).mpr hy
  have hf : f i ∈ H := hp (Metric.mem_ball.mpr ((Metric.mem_ball.mp h₂).trans (half_lt_self hε)))
  have hb : q∈H := by
    apply hp; apply Metric.mem_ball.mpr
    have hz := dist_triangle q (f i) p; rw [dist_eq_norm q (f i)] at hz
    change bill (-3/2) (s i) ≤ ε/2 at h₃
    linarith only [Metric.mem_ball.mp h₂,hz,h₃,he]
  have ht : ‖F q-F (f i)‖≤A*‖q-f i‖ := LipschitzOnWith.norm_sub_le hF hb hf
  have hx : ‖Q-Q'‖≤(A:ℝ)*bill (-3/2) (s i) := by
    rw [show Q=F q from Hq.uniq (rolls _ (Hq.2 ▸ Poly.pass_part Q Hq.1)), show Q'= F (f i) from Hq'.uniq (rolls _ (Hq'.2 ▸ Poly.pass_part Q' Hq'.1))]
    exact ht.trans (mul_le_mul_of_nonneg_left he (by positivity))
  linarith only [hx,h₁]
end YM.Next.Rank.Glimmer
