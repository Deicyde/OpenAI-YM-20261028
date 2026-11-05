import YM.Next.RANK.Pilgrim
import YM.Next.RANK.StrideCost


/-! Reduce E comparisons on actual kernels. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Prayer
open Function Set Lattice Wilson RG Normal Beamer Perch Configuration Glimmer Atlas Filter Station
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {P : Schedule} (A : Levels G) {d p k l n : ℕ}

-- Signed fold; Qmarks on Cover uses genuine chart entries

def looked (K : Normal.Symmetric (Chamber G P k p)) (u v : Cover) : Bridge G :=
    fun x y => (K.cov (body u x) (body v y)).re

lemma called (H : AtlasData G P p) {k l : ℕ} (u : Fin n → Cover) (hp : l≤k) (i j) :
    Γre P H u hp i j=(if i=j then 0 else looked (H.κ k) (u i) (u j))-looked (scope (lines H l hp) (H.κ l)) (u i) (u j) := by
  funext x y; unfold Γre Qmarks; let s (x : Fin n × Address G) := body (P:=P) (k:=k) (p:=p) (u x.1) x.2
  dsimp only
  change ((scope (fun x => Finsupp.single (s x) (1:ℂ)) _).cov _ _+ -(if _=_ then _ else 0)).re=_
  rw [match_name s]
  by_cases he : i=j
  · subst j; simp only [if_true]; change _ = (0 : ℝ)- _; rw [match_name (fun x : Address G => body (u i) x) (H.κ k)]
    change ( (_ + - _ : ℂ)+ -_:ℂ).re=_; simp only [Complex.add_re,Complex.neg_re]; unfold looked; dsimp only [s]; ring
  simp only [he,↓reduceIte]; change ((_ + - _ : ℂ) + - (0:ℂ)).re = _ - _; simp only [neg_zero,add_zero,Complex.add_re,Complex.neg_re]; rfl

-- character estimate port. needed here even if C calendar doesn't enforce enough.

structure MeridianArc (P E R : ℝ) (M : ℕ) (d k p : ℕ) (u v : Cover) (x y : E4) (X : AtlasData G A.S p) : Prop where
  /-- positivity of full curvature kernel need not be assumed for this formal pipeline. -/
  closures : (∀ i,shutter (looked (X.κ k) u v i)) ∧ (∀ j,shutter (fun z => looked (X.κ k) u v z j))
  extent (a b : Degree G) : attends d M a → attends d M b → amount R a*amount R b*‖mourn (gesture a) (gesture b) (looked (X.κ k) u v)‖ ≤ P
  origin (a b : Hub G d 0) : ‖amount R a.val * amount R b.val*mourn (gesture a.val) (gesture b.val) (looked (X.κ k) u v)-
    light a.val b.val x y‖ ≤ E

-- middle comparison consumes arcs at each pair. low from conditional estimate & spectra.

section
variable {A}

lemma penalty (x : Points n) (hx : x∈conf n) (b : ℝ) (d : ℕ) (A : Levels G) (hB : G.Simple) (hb : 5≤ b) :
    ∀ᶠ k in atTop, ∀ hp : Fit A b k x, ∀ (i j : Fin n) (L S : Hub G d 0), i ≠ j →
      let T := tested A b k x; let r := mag A b k
      ‖amount r L.val * amount r S.val * mourn (gesture L.val) (gesture S.val) (collect d (Ship.fitting hp) r G i j) -
        light L.val S.val (T i) (T j)‖ ≤ bill (-4) (clim A k) := by
  suffices H : ∀ᶠ k in atTop, ∀ (i j : Fin n) (L S : Hub G d 0), i≠j → ∀ hp : Fit A b k x,
      let T := tested A b k x; let r := mag A b k
      ‖amount r L.val * amount r S.val * mourn (gesture L.val) (gesture S.val) (collect d (Ship.fitting hp) r G i j) -
        light L.val S.val (T i) (T j)‖ ≤ bill (-4) (clim A k) from H.mono fun _ h hp i j L S hi => h i j L S hi hp
  refine eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun L => eventually_all.mpr fun S => ?_
  have ht : 0 < b := by linarith
  obtain ⟨C,hc,he⟩ := fence (n:=n) L S
  let a := 1/(2:ℝ)
  have hg (v w : KeyIn G d) : ∀ᶠ k in atTop, ∀ p : Fit A b k x,
      ‖(currentX (Ship.fitting p) G d).cov (i,v) (j,w)‖ ≤ a*bill a (clim A k) := Atlas.covered A ht hB hx (by norm_num [a]) _ _
  filter_upwards [eventually_all.mpr fun v => eventually_all.mpr (hg v),(hat_rate A hB).eventually (transports (b:=b + -4) (show a<b + -4 by dsimp [a]; linarith) (C*a))]
    with k hv hh hi hp
  let s:= clim A k
  intro T r
  have hr : 1 ≤ r := by dsimp only [r]; rw [mag_bill]; exact Glimmer.costed _ _ ht.le
  apply le_of_mul_le_mul_left _ (zero_lt_one.trans_le hr)
  refine (he T (Ship.fitting hp) i j hi (a*bill a s) (by unfold a bill; positivity) (fun p q => ?_) _ hr).trans ?_
  · exact (Complex.abs_re_le_norm _).trans (hv p q hp)
  change C*(a* _ ) ≤ r*_;rw [show r=_ from mag_bill A b k,overlap,← mul_assoc]; exact hh
end
end YM.Next.Rank.Prayer
