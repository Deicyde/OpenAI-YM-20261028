import YM.OPE.Trees.Far
/-!
# Families at the boundary of a substep

All-root observables, including horizon coefficients and tested
remainders, inherit the arbitrary-power approximation under a pace Leap.
This lets us prove exactly the power accounting sought at the top, by
appealing to shorter active trees for 'input redactions'. In particular,
detectors never change when considering a larger tree scenery at the root.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Finset Prescription
open scoped Classical Topology BigOperators ContDiff
variable {I J K: Type}[Fintype I][Fintype J]
variable {s:Arboreal I} {x:K→ I→ E4}{i:I}{a b:Finset I}
variable {φ:Filter K} {t:I→ℝ}{T:K→ℝ}{R:K→I→ℝ}{M δ u:ℝ}
section Pricing
variable {G:Gauge} {A:Register G} {S:Table A}{H:DiffPlan S} {P:Prescription H}
    {v:I→ A.Token}

abbrev Presentment (I K:Type)(S:Register G) := K → Finset I → (I→ S.Token) → ℂ -- observable z partial tree b v labels
variable {g g':Presentment I K A}

/-- Try a match to horizon n at i, replacing current b=a by `s.redact a i`.
Act on a Presentment. -/
def alter (s:Arboreal I)(P:Prescription H)(a:Finset I)(v:I→ A.Token)(x:K→ I→ E4)(i:I)(n:ℕ)(g:Presentment I K A)(j:K) :ℂ := g j a v - ∑ w ∈ bands H n, coalesce P (s.inputs a i) (x j) v i w * g j (s.redact a i) (update v i (P.letter w))

def Forever (s:Arboreal I)(P:Prescription H)(x:K→ I→ E4)(a:Finset I)(i:I)(v:I→ A.Token)(φ:Filter K)(T:K→ℝ)(g:Presentment I K A) : Prop := ∀ u:ℝ,∀ᶠ n:ℕ in atTop, RateLE φ T (s.alter P a v x i n g) u

variable (h:s.Forever P x a i v φ T g)
lemma Forever.monoEq (h:s.Forever P x a i v φ T g)
    (hx:(fun j=>g j a v)=ᶠ[φ] fun j=> g' j a v)(hv:∀ y:I→A.Token, (fun j=>g j (s.redact a i) y)=ᶠ[φ] fun j=>g' j (s.redact a i) y): s.Forever P x a i v φ T g':=by intro u; filter_upwards [h u] with n hn; apply hn.congr; filter_upwards [hx,(eventually_all_finset (bands H n)).2 (fun y _=> hv (update v i (P.letter y)))] with j hj he; exact congrArg₂ (·-·) hj (sum_congr rfl fun k hk=> congr_arg _ (he k hk))
lemma Forever.delivers {f:K→ℂ}{c:ℝ}(h:s.Forever P x a i v φ T g)(hf:RateLE φ T f c) :s.Forever P x a i v φ T (fun j b p=> g j b p*f j):=by
    intro u; filter_upwards [h (u-c)] with n hN; apply RateLE.congr ((hN.mul hf).mono (by simp)); filter_upwards with j; unfold alter; rw [sub_mul,sum_mul]; exact congr_arg _ (sum_congr rfl fun i hi=>mul_assoc ..)
lemma Forever.delivers' {f:K→ℂ}{c:ℝ}(h:s.Forever P x a i v φ T g)(hf:RateLE φ T f c) :s.Forever P x a i v φ T (fun j b p=> f j*g j b p):=by
    have he:=h.delivers hf; apply he.monoEq (Eventually.of_forall _) (fun y=>Eventually.of_forall _); all_goals intros; exact mul_comm .. 
lemma Forever.many {L:Type*}{b': Finset L}(f:L→Presentment I K A)(h':∀ j∈b', s.Forever P x a i v φ T (f j))(hT:Tendsto T φ atTop): s.Forever P x a i v φ T (fun j b p=> ∑ u∈ b',f u j b p):=by
    intro u; filter_upwards [(eventually_all_finset b').2 (fun i hi=>h' i hi u)] with n hn; apply RateLE.congr (RateLE.sum hT hn); filter_upwards with j; unfold alter; rw [sum_sub_distrib]; refine congr_arg _ ?_ ; simp only [mul_sum]; rw [Finset.sum_comm]
lemma Forever.sub (h:s.Forever P x a i v φ T g)(hh:s.Forever P x a i v φ T g')(hT:Tendsto T φ atTop): s.Forever P x a i v φ T (fun j b p=> g j b p-g' j b p):=by
    intro u; filter_upwards [h u, hh u] with n hx he; apply RateLE.congr (hx.sub he hT); filter_upwards with j; unfold alter; simp only [mul_sub,sum_sub_distrib]; ring
end Pricing

variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book} (U:Spec.Final C F S)
    {P:Prescription U.sector.derivatives}[φ.NeBot]
    (v:I→ C.book.Token)(ξ:Mode U.sector.derivatives) {y:K→J→ E4} (q:J→ C.book.Token)(L:K→ Viewers U)
local notation "T!"=> (fun i=>s.fullLife (R i))
variable (h:s.Coterie φ t M δ x R)(hp:P.Coherent)(H:Services C F S) (ht:s.Active a)(he:s.Leap t a i)
include h H hp ht he
lemma useful_product (hz:Backdrop φ (fun i=>x i s.root) y) : s.Forever P x a i v φ T! (fun j b' v'=> whole (spectator U (L j)) (s.live b') (x j) v' (y j) q):= strict_expands U v q L h hp H hz ht he
lemma useful_coeff : s.Forever P x a i v φ T! (fun j b' v'=> coalesce P (s.live b') (x j) v' s.root ξ):= by
    let f (u:Exterior C.book) : Presentment I K C.book:= fun j b' v'=> whole S (s.live b') (x j) v' (register u (x j s.root)) u.letter
    have hx(u): s.Forever P x a i v φ T! (f u):= useful_product U v u.letter (fun _=>none) h hp H ht he (shelf u (fun j=> x j s.root))
    let Ξ:= P.sheet ξ; apply Forever.monoEq (g:= fun j b v=> ∑ u∈ Ξ.support, Ξ u*f u j b v) (Forever.many (fun u j b v=> Ξ u * f u j b v) (fun j hj=> (hx j).delivers' (RateLE.const _ h.time)) h.time) (wrapDetector U v ξ h H a ht).symm (fun y=> (wrapDetector U y ξ h H _ (redacted ht he.inner)).symm) -- defeq
lemma useful_flux (hz:Backdrop φ (fun i=>x i s.root) y)(n:ℕ) : s.Forever P x a i v φ T! (fun j b v=> flux P (spectator U (L j)) (s.live b) (x j) v s.root (y j) q n):=(useful_product U v q L h hp H ht he hz).sub (Forever.many (fun w j b v=> coalesce P (s.live b) (x j) v s.root w * pickOne P (spectator U (L j)) (x j) s.root w (y j) q) (fun w hw=> (useful_coeff U v w h hp H ht he).delivers (inserted_cost U w q L h H hz s.root)) h.time) h.time
end YM.OPE.Arboreal
