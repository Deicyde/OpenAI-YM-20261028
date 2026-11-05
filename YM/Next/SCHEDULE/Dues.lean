import YM.Next.SCHEDULE.Pre
import YM.Next.SCHEDULE.Vicinity
import YM.Work.C01
import YM.Work.E01


/-!
# Delay gates: the band

Full names important. Work at smoothing indices j/old with `L` actual,
`x` COARSE HAT BETA and `y=x+c`, `c=𝔟 log L`. Use this 
sufficient currency of entrance tests. `bundle` is a common envelope for the
fixed powers and constants billed *ONCE*. Inherited `q` power repeatedly has
pre-L factor instead. No conclusion that either set of estimates holds! The
`1/(16*C)` and half cone tests below on the post part of a coefficient must be
established, e.g. by making `betaEntry` floor also ≥ a threshold of the
producer for all such profiles; see availability of arbitrary increases in
`Post`. They are not verified o_L(1) statements about physics.

Include also a secondary mode horde here: numerical gates with p changed to
P = `watch (3/2)` and B replaced by B², but STILL using the loop gate of
the *original* profile.

Intended for restarts on plateau.

Nothing here claims this.

Ever requiring p^θ ≤ P
at fixed plateau by increase of delay would in fact fail.

Later modules
coordinate Work windows and iteration costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling
open Filter Function RG RG.Supply Bid Lattice Clock
open scoped Topology

/-- Besides the ordinary profile, much smaller thresholds can pass these
*numerical* gate types (use `watch`). No L-, period- or x-dependent shape.
-/
structure Instrument where
  center : ℝ
  bulk : ℕ
  below : center ≤ 2
  above : 1 < center
  buys : 1 ≤ bulk

namespace Instrument

def plain : Instrument := ⟨2,1,le_rfl,by norm_num,le_rfl⟩
def chorus : Instrument := ⟨3/2,2,by norm_num,by norm_num,by norm_num⟩

def P (M : Instrument) := Clock.watch M.center
def body (M : Instrument) x := Clock.cover x^M.bulk
def w (M : Instrument) x := Real.exp (-(M.P x)^((1:ℝ)/5))

def t (M : Instrument) x := Clock.gap x * M.P x
end Instrument

/-- Loop exponent always in original convention. -/
def LevelCost (θ x : ℝ) := Instrument.plain.P x ^ θ
def δE (x : ℝ) := Clock.gap x ^ ((11:ℝ)/5)

/-- NOT cost pre-L. Envelope valuations after L, supply estimates at values
(as opposed to bounding Norm through existential `≪`). `rate` a minimum even
for purposes accruing largest-L payouts (positive fixed here). Choose `power`
for source cost exponent after L as well. -/
structure Postage where
  H : ℝ
  D : ℕ
  rate : ℝ
  power : ℝ
  h_ge : 1 ≤ H
  pos : 0 < rate
  pos_p : 0 < power

namespace Postage
variable (A : Postage)

def bundle (M : Instrument) (θ x y : ℝ) := A.H * (1 + (M.body x:ℝ) + M.P y + 2*LevelCost θ y)^A.D

/-- bound currency. `g=gap actual_banded_beta`; polynomials in B,Λ
hard-billed for **same x,y,θ**, cf . -/
def residual (M : Instrument) (θ x y g : ℝ) :=
    A.bundle M θ x y *
      (g^ (3:ℕ) + g⁻¹^A.D * (Real.exp (-A.rate * M.body x)
        + Real.exp (-A.rate*(M.P y)^ (2:ℕ)/(1+(M.body x:ℝ))^A.D)))

/-- Lump Cstep for respective pre-L C_J factors (after projection and covers).
`1/(16*C)` accommodates post-L part of q if sufficiently delayed. -/
def switch (M : Instrument) (C L θ x y g : ℝ) :=
    (C/L+1/(16*C))*δE y + A.residual M θ x y g
end Postage

/-- Enlarged possible actual band (see  re-expression), including endpoints. `gap` is evaluated at that actual β, all
hard prices quoted at FIXED x hatted. -/
def inBand (x β : ℝ) := β ∈ Set.Icc (x/4) (4*x)

lemma trial_in {G : Gauge} {a : Levels G} {m : ℕ} {β : ℝ} (h : β ∈ Shoot.band a m) :
    inBand (a.clock.hatBeta m) β := by
  obtain ⟨h1,h2⟩ := h; have := a.fits.delayed m; constructor <;> linarith

lemma band_gap (x β : ℝ) (hx : 0 < x) (h : inBand x β) :
    Clock.gap x/2 ≤ Clock.gap β ∧ Clock.gap β ≤ 2*Clock.gap x := by
  obtain ⟨ha,hb⟩ := h
  have hp : 0<β := by linarith
  unfold Clock.gap
  have he := Real.sqrt_pos.2 hx; have he' := Real.sqrt_pos.2 hp
  constructor <;> field_simp <;> nlinarith [Real.sq_sqrt hx.le,Real.sq_sqrt hp.le]

/-- Choose symmetric adjacent comparisons within certainty θm. `R≈2`, can be
made arbitrarily close to 1. Including w across changed profile. Use these
comparisons at every step, not just eventually in m. -/
def twins (f : ℝ → ℝ) (x y R : ℝ) := f x ≤ R*f y ∧ f y ≤ R*f x

structure Alike (M : Instrument) (x y R : ℝ) : Prop where
  temp : twins M.t x y R
  peek : twins M.P x y R
  direct : twins Instrument.plain.P x y R
  gap : twins Clock.gap x y R
  mass : twins (fun x => (M.body x:ℝ)) x y R
  gas : twins M.w x y R

/-- τ includes t-handoff through profile. j→i path loop still uses `plain`.
`paidG` already after L min e.g. rate/8, possibly even smaller because other
transition must use same post-cost for Move. -/
structure BandGate {G : Gauge} (s : Survey G) (q : Quote) (e : Exchange) (M : Instrument) (A : Postage)
    (j i : ℕ) (L θ θ' paidG c x : ℝ) : Prop where
  -- entrance comparisons
  late : 1 < x ∧ 1 < x+c
  scale : 9 ≤ M.body x ∧ 9 ≤ M.body (x+c)
  seats : 1 ≤ M.P x ∧ 1 ≤ M.P (x+c)
  plate : M.t x ≤ 1 ∧ M.t (x+c) ≤ 1
  adjacent : Alike M x (x+c) 2
  -- λ/paths closed
  emit : q.finish.loop j i * L^ (4:ℕ) ≤ LevelCost θ' x
  reset : LevelCost θ (x+c) ≤ 2*LevelCost θ' x
  -- force handoff (include case top with rate* too via other booking)
  save : Real.exp (-paidG*(M.P (x+c))^ (2:ℕ)) ≤ M.w x
  -- conditional response prices are uniform in β INPUT band
  budgets β : inBand (x+c) β →
    let y := x+c; let g := Clock.gap β; let C := e.cost
    C*A.switch M C L θ x y g + A.bundle M θ x y*(M.t x)^ (3:ℕ) < δE x ∧
      C*A.switch M C L θ x y g ≤ (M.t x)^ (2:ℕ) ∧
      A.H*Real.exp (-A.rate*(M.t y/g)^ (2:ℕ)) ≤ Real.exp (-paidG*(M.P y)^ (2:ℕ)) ∧
      A.H*(1+(M.body x:ℝ))^A.D/M.P y+g^A.power ≤ (1:ℝ)/L^((2:ℝ)/5)

open Real
lemma Instrument.support (M : Instrument) (R : ℝ) (hR : 1 < R) :
    ∀ᶠ x in atTop, ∀ a b, near x a → near x b → Alike M a b R := by
  have hs := sqrt_pos.mpr (show 0<R from lt_trans zero_lt_one hR)
  have hw := sq_sqrt (show 0≤R by linarith)
  have hg : 1 < √R := (Real.lt_sqrt (by positivity)).mpr (by simpa using hR)
  let p := R^((M.bulk:ℝ))⁻¹
  have hp : (p:ℝ)>1 := Real.one_lt_rpow hR (inv_pos.mpr (by exact_mod_cast (show 0<M.bulk from M.buys)))
  have h1 : Similar M.P := by simpa only [Instrument.P, Real.rpow_one] using similar_watch_power M.center 1
  have h2 : Similar Clock.gap := by simpa using similar_gap_power 1
  have h3 : Similar plain.P := by simpa [P] using similar_watch_power plain.center 1
  have h4 : Similar M.w := by unfold w; simpa only [P, neg_one_mul] using similar_gas M.center ((1:ℝ)/5) 1
  filter_upwards [h1 _ hg,h2 _ hg,h3 _ hR,h4 _ hR, Clock.similar_cover _ hp, advance (eventually_gt_atTop (0:ℝ))] with x ha hb hc hd he hf
  have hr (a b : ℝ) (ax : near x a) (bx : near x b) :
      M.t a ≤ R*M.t b ∧ M.P a ≤ R*M.P b ∧ Clock.gap a ≤ R*Clock.gap b ∧ (M.body a:ℝ) ≤ R * (M.body b:ℝ) := by
    have hp := ha a b ax bx; have hh := hb a b ax bx
    have hxP : 0 < M.P a := wp M.center a; have hyP : 0 < M.P b := wp M.center b
    have hxg := gp (hf a ax); have hyg := gp (hf b bx)
    have ht : √R ≤ R := by nlinarith
    refine ⟨?_,hp.trans (mul_le_mul_of_nonneg_right ht hyP.le), hh.trans (mul_le_mul_of_nonneg_right ht hyg.le),?_⟩
    · have hk:=mul_le_mul hh hp hxP.le (mul_nonneg hs.le hyg.le)
      unfold Instrument.t
      refine hk.trans_eq ?_
      nth_rw 3 [← hw]; ring
    have hu := pow_le_pow_left₀ (show 0≤(Clock.cover a:ℝ) by positivity) (he a b ax bx) M.bulk
    rw [mul_pow,show p^M.bulk=R from rpow_inv_natCast_pow (by linarith) (by have := M.buys; omega)] at hu
    exact_mod_cast hu
  intro a b ax bx
  obtain ⟨h1,h2,h3,hv⟩:=hr a b ax bx; obtain ⟨s1,s2,s3,sv⟩:=hr b a bx ax
  exact ⟨⟨h1,s1⟩,⟨h2,s2⟩,⟨hc a b ax bx,hc b a bx ax⟩,⟨h3,s3⟩,⟨hv,sv⟩,⟨hd a b ax bx,hd b a bx ax⟩⟩
end YM.Next.Scheduling
