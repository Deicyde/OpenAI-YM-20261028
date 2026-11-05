import YM.Extra.ITERATION_NO_LOSS.Margins
import YM.Extra.ITERATION_NO_LOSS.PathHit
import YM.Extra.ITERATION_NO_LOSS.Radius

/-!
# Regenerate the operating exponent, cover geometry and budgets after L

Use in parallel with `Post.lean`'s path worksheet. `Census` can be chosen
once path numerics are known (otherwise anticipate them beforehand); its
values and the full support exponents/desired reserves **before** enlarging
floorL. Halo is in cover radii; not allowed to depend on L. Every finite
additional width/exponent request needs a sufficient receipt, not automatic
because larger floors are *allowed*. `Fuel` in this file means numeric
requests, not the root estimates in Overlay. No new density defined.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration.Rebuild
open Filter Function Lattice Wilson RG RG.Supply Precision Pressure Scales 
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {S : Sheet G} {D : Rolls S} {Θ : Protection D} {W : Supply.Delays Θ} {Y : Bar W} {I : Wait Y}

/-- halo/exponent reserves can depend on both possible transitions and other
pre-L requests. s=0 allowed. `leading` pays C_J on q, E' and reset.
Can enlarge inherited stationary thresholds *before* actual D is chosen.
-/
structure Census where
  halo : ℕ → ℕ → ℕ
  reserve : ℕ → ℕ → ℝ
  leading : ℕ → ℕ → ℝ
  reserve_nonneg j k : 0 ≤ reserve j k
  pos j k : 0 < leading j k

structure Open (V : Census) (p : Sheet G) : Prop where
  project (j k) : k ≤ j → j ≤ k+1 →
    20*(Shapes.pad (V.halo j k+9):ℝ)*((p.profile k).supportExponent+V.reserve j k) ≤ (p.profile j).supportExponent*p.floorL j
  afford (j k) : k ≤ j → j ≤ k+1 → 8*(V.leading j k)^2 ≤ (p.floorL j:ℝ)

theorem more (V : Census) (p : Sheet G) : ∃ v : ℕ → ℕ, ∀ n : ℕ → ℕ, (∀ i, v i ≤ n i) → p.floorL ≤ n ∧
    Open V {p with floorL := n} := by
  let bill (j k : ℕ) : ℝ := max (20*(Shapes.pad (V.halo j k+9):ℝ)*((p.profile k).supportExponent+V.reserve j k)/(p.profile j).supportExponent)
    (8*(V.leading j k)^2)
  choose b hb using fun j k => exists_nat_gt (bill j k)
  refine ⟨fun j => max (max (b j j) (b j (j-1))) (p.floorL j),fun n hn => ⟨fun j => (le_max_right ..).trans (hn j),?_⟩⟩
  have he (j k) (hk : k≤j) (hj : j≤k+1) : bill j k ≤ n j := by
    apply (hb j k).le.trans; exact_mod_cast le_trans (le_max_of_le_left (by
      rcases (show k=j ∨ k=j-1 by omega) with rfl|h; exact le_max_left ..; rw [h]; exact le_max_right ..)) (hn j)
  refine ⟨fun j k hk hj => ?_, fun j k hk hj => (le_max_right ..).trans (he j k hk hj)⟩
  exact ((div_le_iff₀ (p.profile j).price_pos).mp ((le_max_left ..).trans (he j k hk hj))).trans_eq (mul_comm ..)

/-- All before buying an
actual band/wait. e.g. leak a post-L `o_L(1)` uniform in period/couplings,
actual smallness required at each entrance.

Does NOT compute such a rate for
the integral! -/
structure Fuel {G : Gauge} {S : Sheet G} (D : Rolls S) where
  cost : ℕ → ℕ → ℝ
  rate : ℕ → ℕ → ℝ
  power : ℕ → ℕ → ℕ
  leak : ℕ → ℕ → ℝ → ℝ
  nonnegative j k : 0 ≤ cost j k
  positive j k : 0 < rate j k
  fades j k : Tendsto (leak j k) atTop (𝓝 0)

namespace Fuel
variable (F : Fuel D)

def strength (j : ℕ) := min (F.rate j j) (F.rate j (j-1))/4
lemma strength_pos (j : ℕ) : 0 < F.strength j := by unfold strength; have := lt_min (F.positive j j) (F.positive j (j-1)); positivity
lemma strength_le {j k} (hk : k ≤ j) (hj : j ≤ k+1) : F.strength j ≤ F.rate j k / 4 := by
  unfold strength; gcongr; rcases (show k=j ∨ k=j-1 by omega) with rfl|rfl; exact min_le_left ..; exact min_le_right ..

def output (j k : ℕ) (x θ : ℝ) := poly (F.cost j k) (F.power j k) x (betaF G x (D.L j)) θ

def weak (S : Census) (j k : ℕ) (x θ b : ℝ) :=
    let y := betaF G x (D.L j)
    let C := S.leading j k
    C*((C/(D.L j).val + F.leak j k x) * unforced y + bill (F.cost j k) (F.rate j k) (F.power j k) x y θ b)

def hard (j k : ℕ) (x b : ℝ) := marked (F.cost j k) (F.rate j k) (betaF G x (D.L j)) b
end Fuel

structure Entrance (S' : Census) (F : Fuel D) (Θ : Protection D) (j k : ℕ) (x : ℝ) : Prop where
  geometry : radiusB (betaF G x (D.L j)) ≤ 2*radiusB x ∧ radiusB x ≤ 2*radiusB (betaF G x (D.L j))
  small : temp (betaF G x (D.L j)) ≤ 2*temp x ∧ temp x ≤ 2*temp (betaF G x (D.L j))
  fine : Shapes.broad (S'.halo j k) (radiusB (betaF G x (D.L j))) ((S.profile j).supportExponent + S'.reserve j k) (S.profile j).width
  coarse : Shapes.broad (S'.halo j k) (radiusB x) ((S.profile k).supportExponent + S'.reserve j k) (S.profile k).width
  output : F.output j k x (Θ.theta j) * temp x^ (3:ℕ) ≤ unforced x/8
  weak (b : ℝ) : betaF G x (D.L j) / 2 ≤ b → b ≤ 2*betaF G x (D.L j) → F.weak S' j k x (Θ.theta j) b ≤ (3/8)*unforced x
  hard (b : ℝ) : betaF G x (D.L j) / 2 ≤ b → F.hard j k x b ≤ Real.exp (-(F.strength j)*meter (betaF G x (D.L j))^(2:ℕ))
  time : Real.exp (-(F.strength j)*meter (betaF G x (D.L j))^ (2:ℕ)) ≤ forced x

lemma geometry (a : ℝ) : ∀ᶠ x : ℝ in atTop, (radiusB (x+a) ≤ 2*radiusB x ∧ radiusB x ≤ 2*radiusB (x+a)) ∧
    (temp (x+a) ≤ 2*temp x ∧ temp x ≤ 2*temp (x+a)) := by
  have h := Work.E09.temp_ratio a
  have he : Tendsto (fun x : ℝ => x+a) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  filter_upwards [Stock.stepsize a, he.eventually (Stock.stepsize (-a)),eventually_gt_atTop (0:ℝ),h.eventually (ge_mem_nhds (show (1:ℝ)<2 by norm_num)),
    h.eventually (le_mem_nhds (show (1/2:ℝ)<1 by norm_num))] with x h1 h2 hx hmax hmin
  change Stock.scaleB (x+a+-a)^2≤_ at h2
  rw [add_neg_cancel_right] at h2
  have ht := Work.E09.temp_pos hx
  refine ⟨?_, (div_le_iff₀ ht).mp hmax, by linarith only [(le_div_iff₀ ht).mp hmin]⟩
  change Stock.scaleB (x+a) ≤ 2*Stock.scaleB x ∧ Stock.scaleB x ≤ 2*Stock.scaleB (x+a)
  constructor <;> nlinarith

lemma cover_grows : Tendsto (fun x => (radiusB x:ℝ)) atTop atTop := tendsto_atTop_mono (fun x => Nat.le_ceil _) ((tendsto_pow_atTop (n:=2)
    (by decide)).comp Real.tendsto_log_atTop)
lemma eventual_broad (s : ℕ) (A σ a : ℝ) (he : 0 < σ) : ∀ᶠ x in atTop, Shapes.broad s (radiusB (x+a)) A σ :=
    (((cover_grows.comp (tendsto_atTop_add_const_right _ _ tendsto_id)).atTop_mul_const he).eventually_ge_atTop _)

lemma enters {V : Census} (F : Fuel D) (Θ : Protection D) (hG : G.Simple) (h : Open V S) (j k : ℕ) (hk : k ≤ j) (hj : j ≤ k+1) :
    ∀ᶠ x in atTop, Entrance V F Θ j k x := by
  let s := (D.L j).val; let a := G.slopeConstant*Real.log s; let c := F.cost j k; let r := F.rate j k; let C := V.leading j k
  have hL : (1:ℝ) ≤ s := by exact_mod_cast (D.L j).pos
  have ha : 0 ≤ a := mul_nonneg (Gauge.slopeConstant_pos hG).le (Real.log_nonneg hL)
  have hC := V.pos j k; change 0<C at hC
  have hs : 8*C^2 ≤ (s:ℝ) := (h.afford j k hk hj).trans (by exact_mod_cast (D.large j).need)
  have hf := pay_forced a c r (F.strength j) (F.positive j k) (F.strength_pos j) (F.strength_le hk hj)
  have he := pay_regular C c r a (Θ.theta j) (F.power j k) hC (F.nonnegative ..) (F.positive ..)
  have hl : 0 < ((1/8:ℝ)/C) := by positivity
  filter_upwards [he,hf,geometry a,eventually_gt_atTop (1:ℝ),(F.fades j k).eventually (ge_mem_nhds hl),
    eventual_broad (V.halo j k) ((S.profile j).supportExponent+V.reserve j k) (S.profile j).width a (S.profile j).width_pos,
    eventual_broad (V.halo j k) ((S.profile k).supportExponent+V.reserve j k) (S.profile k).width 0 (S.profile k).width_pos]
    with x he hf hg hx hl hB hB'
  rw [add_zero] at hB'
  refine ⟨hg.1,hg.2,hB,hB', he.1, fun b hb hb' => ?_,fun b => hf.2 b,hf.1⟩
  change C*((C/s+F.leak j k x)*unforced (x+a)+ bill c r _ x (x+a) _ b) ≤ _
  have he := he.2 b hb hb'
  have ht := unforced_mono (x:=x) (by linarith) (le_add_of_nonneg_right ha)
  have hu : 0 ≤ unforced (x+a) := by unfold unforced Vac.Numbers.Hat; positivity
  have hv : C*(C/s + F.leak j k x) ≤ 1/4 := by
    rw [mul_add, ← mul_div_assoc]; have hp : C*C/(s:ℝ)≤1/8 := (div_le_iff₀ (by positivity)).mpr (by linarith)
    linarith only [(le_div_iff₀ hC).mp hl,hp]
  linarith only [mul_le_mul_of_nonneg_right hv hu, he,ht]

structure Cool (V : Census) (F : Fuel D) (W : Supply.Delays Θ) : Prop where
  pay (j k : ℕ) : k ≤ j → j ≤ k+1 → ∀ x : ℝ, W.betaEntry j ≤ x → Entrance V F Θ j k x

lemma prices {V : Census} (F : Fuel D) (W : Supply.Delays Θ) (hG : G.Simple) (hv : Open V S) : ∃ W' : Supply.Delays Θ,
    W'.shells = W.shells ∧ W'.growth=W.growth ∧ W'.scaleEntry=W.scaleEntry ∧ W.betaEntry ≤ W'.betaEntry ∧ Cool V F W' := by
  have he j (k : ℕ) : ∃ x : ℝ,k ≤ j → j ≤ k+1 → ∀ t : ℝ,x ≤ t → Entrance V F Θ j k t := by
    by_cases h : k ≤ j ∧ j ≤ k+1
    · exact (eventually_atTop.mp (enters F Θ hG hv j k h.1 h.2)).imp fun _ ht _ _ => ht
    exact ⟨0,fun u v => False.elim (h ⟨u,v⟩)⟩
  choose e he using he
  refine ⟨{W with betaEntry := fun j => max (W.betaEntry j) (max (e j j) (e j (j-1)))}, rfl,rfl,rfl,fun _ => le_max_left .., ⟨fun j k hk hj x hx => ?_⟩⟩
  refine he j k hk hj x (le_trans (le_max_of_le_right ?_) hx)
  rcases (show k=j ∨ k=j-1 by omega) with rfl|rfl; exact le_max_left ..; exact le_max_right ..
lemma Cool.raise {V : Census} {F : Fuel D} (h : Cool V F W) {W' : Supply.Delays Θ} (ht : W.betaEntry ≤ W'.betaEntry) : Cool V F W' :=
  ⟨fun j k hk hj x hx => h.pay j k hk hj x ((ht j).trans hx)⟩
end YM.Extra.Iteration.Rebuild
