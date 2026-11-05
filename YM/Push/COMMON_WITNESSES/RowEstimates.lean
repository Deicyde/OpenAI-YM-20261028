import YM.Push.COMMON_WITNESSES.RankBills
import YM.Work.A15

/-!
# From the ROOT bills to unselected tests

Use only the very projections/points/tables which are converging. No appeal
to `Valid` at RCorrected, which would be circular. For each k get estimates
from the finite root hypotheses, including pair with exact centering and unit.
Here we're only using ONE occupied cell to test moments; in phase assembly
we'll then use the `CheapBill`s again (there full replicas are important).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Common
open Function Filter Set MeasureTheory Extraction Wilson Lattice Cells Next.Extract
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

private lemma inOne {G : Gauge} {n : Side} (T : Tiling n) {β} (h : Seam G n β) (F : Config G n → ℂ)
    (H : Interior (T.chamber 0) F) : ‖moment β F‖ ≤ T.rootTest β F := by
  have hu : Injective (fun (_ : Fin 1) => (0:T.Cell)) := fun _ _ _ => Subsingleton.elim ..
  simpa using T.planted h (fun _ : Fin 1 => 0) hu (fun _ => F) (fun _ => H)

private lemma less {n : Side} {G : Gauge} {K : Set (Site n)} {F : Config G n → ℂ} (h : Interior K F) (a : ℂ) :
    Interior K (fun q => F q-a) := by
  simpa [sub_eq_add_neg] using (h.plus (Interior.constant K (-a)))

/- Rank-field entry estimates at all k, table D is either unselected or
one of the phase tables obtained through the assembly. These bounds quantify
over only the prescribed basis and placements. E.g. no comparison of off-grid
kernels at small scale inferred. -/
variable {G : Gauge} {C : Family G} {d : ℕ} {T : Table C.book}
variable {X : Columns C T d} (Y : X.Trials)

structure Prices (D : Table C.book) : Prop where
  one (k i c s) : ‖D.expect [Retain.plant Y k i c s]- Y.singleton k i c s‖ ≤ Y.gap k
  pair (k i c s u) : s<u → ‖D.expect [Retain.plant Y k i c s,Retain.plant Y k i c u]- Retain.free2 Y k i c s u‖ ≤
      Y.gap k + (‖Y.singleton k i c s‖+‖Y.singleton k i c u‖)*Y.gap k

variable {f : Extraction.Order} (η : Setup Y) (h : f.PointLimits C T) {z : ProbeID X → ℕ → C.label d}
variable (hp : Response Y f z)

include η h hp in
/-- Can keep the two-stage limit here, aliasing lifts and labels exactly. -/
lemma probing (k i c) {n : ℕ} (u : Fin n → Fin ((X.row i).extra+1)) (H : Injective u) :
    f.limits (fun p => Extraction.Order.grid C (Y.depth k) (Y.mark k i ∘ u)∈ Cyclic C.S p n)
      (fun N p => moment (C.beta N p) (fun U => ∏ j, Y.weigh k N p i c (u j) U))
      (T.expect (List.ofFn fun j => Retain.plant Y k i c (u j))) := by
  let a := Extraction.Order.grid C (Y.depth k) (Y.mark k i ∘ u)
  have ha : a ∈ YM.generic n := fun s => (η.generic k i s).comp H
  let r (s) := Columns.Trials.names (X:=X) i c (u s)
  have he := keeps_moments (k:=Y.depth k) (d:=fun _ : Fin n => d) C f T _ ha h
      (fun j => Y.later k (r j)) (fun N p j => Y.lift k N p (r j)) (fun j => hp.limits (k,r j))
  rw [show T.expect (List.ofFn fun j => Retain.plant Y k i c (u j)) = _ from T.readAt (fun j => Retain.token Y k i c (u j)) a]
  exact he

private lemma bill1 (k N p : ℕ) (i c s) (W : Tiling (C.side N p))
    (h : Interior (W.chamber 0) (Y.weigh k N p i c s)) :
    moment (C.beta N p) (Y.subtract1 k N p i c s) =
      moment (C.beta N p) (Y.weigh k N p i c s) - Y.singleton k i c s := by
  unfold moment Columns.Trials.subtract1
  rw [integral_sub (h.integrable _) (integrable_const _),integral_const]; simp

/-- The paired root estimate isn't a bound on `F*G-(a*b+c)`; need the two
lower bills as well to give the usual kernel estimate. -/
private lemma bill2 (k N p : ℕ) (i c s t) (W : Tiling (C.side N p))
    (h : Interior (W.chamber 0) (Y.weigh k N p i c s)) (he : Interior (W.chamber 0) (Y.weigh k N p i c t)) :
    moment (C.beta N p) (Y.subtract2 k N p i c s t) = moment (C.beta N p) (fun q => Y.weigh k N p i c s q * Y.weigh k N p i c t q)
       - Y.singleton k i c s * moment (C.beta N p) (Y.weigh k N p i c t)
       - Y.singleton k i c t * moment (C.beta N p) (Y.weigh k N p i c s)
       + (Y.singleton k i c s * Y.singleton k i c t - Y.cumulant k i c s t) := by
  let F := Y.weigh k N p i c s
  let P := Y.weigh k N p i c t
  let a := Y.singleton k i c s
  let b := Y.singleton k i c t
  let w := Y.cumulant k i c s t
  have hu (q : Config G (C.side N p)) : Y.subtract2 k N p i c s t q = F q*P q - a*P q - b*F q + (a*b-w) := by
    dsimp [F,P,a,b,w,Columns.Trials.subtract1,Columns.Trials.subtract2]; ring
  let β := C.beta N p
  let μ := law G (C.side N p) β
  have hf : Integrable (fun q => F q*P q) μ := (h.times he).integrable _
  have hw : Integrable (fun q => a*P q) μ := ((he.integrable _).const_mul a)
  have hy : Integrable (fun q => b*F q) μ := (h.integrable _).const_mul b
  unfold moment
  rw [show Y.subtract2 k N p i c s t = _ from funext hu]
  have hv : Integrable (fun q => F q*P q - a*P q) μ := hf.sub hw
  have hm : Integrable (fun q => F q*P q - a*P q - b*F q) μ := hv.sub hy
  rw [integral_add hm (integrable_const _), integral_sub hv hy, integral_sub hf hw,
      integral_const_mul, integral_const_mul, integral_const]; simp [F,P,a,b,w,μ,β]

variable (hy : ∀ N p, Seam G (C.side N p) (C.beta N p))
variable (hq : ∀ k ε, 0<ε → CheapBill Y f k ε)

-- Include proofs from the exact extraction.
include η h hp hy hq

theorem unselected_prices : Prices Y T := by
  have hl (k i c s) : Tendsto (fun u : ℕ × ℕ => moment (C.beta u.1 u.2) (Y.weigh k u.1 u.2 i c s)) f.fuse
      (𝓝 (T.expect [Retain.plant Y k i c s])) := by
    have hI : Injective (fun _ : Fin 1 => s) := fun _ _ _ => Subsingleton.elim ..
    have ht := probing Y η h hp k i c _ hI
    simpa using Extraction.Order.along ht
  have han (k i c s) : ‖T.expect [Retain.plant Y k i c s]- Y.singleton k i c s‖ ≤ Y.gap k := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hw := ((hl k i c s).sub_const (Y.singleton k i c s)).norm
    apply le_of_tendsto hw
    change ∀ᶠ u : ℕ × ℕ in f.fuse, ‖moment (C.beta u.1 u.2) (Y.weigh k u.1 u.2 i c s) - Y.singleton k i c s‖ ≤ Y.gap k + ε
    rw [Extraction.Order.fused]
    refine (hq k ε hε).mono fun v hv => hv.mono ?_
    rintro j ⟨w,W⟩
    obtain ⟨H,Gt,_⟩ := W i c s
    rw [← bill1 Y k _ _ i c s _ H]
    exact (inOne _ (hy _ _) _ (less H _)).trans Gt
  refine ⟨han,?_⟩
  intro k i c s t Hst
  let a := Y.singleton k i c s
  let b := Y.singleton k i c t
  let x := Retain.plant Y k i c
  let w := Y.cumulant k i c s t
  let y := T.expect [x s,x t]-a*T.expect [x t]-b*T.expect [x s]+(a*b-w)
  have hb : ‖y‖ ≤ Y.gap k := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hI : Injective (![s,t]) := by
      intro r u
      fin_cases r <;> fin_cases u <;> simp [Hst.ne,Hst.ne']
    have ht := probing Y η h hp k i c _ hI
    have ht : Tendsto (fun u : ℕ × ℕ => moment (C.beta u.1 u.2)
        (fun q => Y.weigh k u.1 u.2 i c s q * Y.weigh k u.1 u.2 i c t q)) f.fuse (𝓝 (T.expect [x s,x t])) := by
      simpa [x,Fin.prod_univ_succ] using Extraction.Order.along ht
    have he := (((ht.sub ((hl k i c t).const_mul a)).sub ((hl k i c s).const_mul b)).add_const (a*b-w)).norm
    apply le_of_tendsto he
    let p (N P : ℕ) := moment (C.beta N P) (fun q => Y.weigh k N P i c s q * Y.weigh k N P i c t q) -
      a*moment (C.beta N P) (Y.weigh k N P i c t) - b*moment (C.beta N P) (Y.weigh k N P i c s) + (a*b-w)
    change ∀ᶠ u : ℕ × ℕ in f.fuse, ‖p u.1 u.2‖ ≤ Y.gap k + ε
    rw [Extraction.Order.fused]
    refine (hq k ε hε).mono fun v hv => hv.mono ?_
    rintro j ⟨w,W⟩
    have H := (W i c s).1
    have H' := (W i c t).1
    have hw := bill2 Y k _ _ i c s t _ H H'
    change _ = p _ _ at hw
    change ‖p _ _‖ ≤ _
    rw [← hw]
    exact (inOne _ (hy _ _) _ (less ((less H a).times (less H' b)) _)).trans ((W i c s).2.2 t Hst)
  change ‖T.expect [x s,x t] - (w+a*b)‖ ≤ Y.gap k+(‖a‖+‖b‖)*Y.gap k
  rw [show T.expect [x s,x t] - (w+a*b) = y + (a*(T.expect [x t]-b)+b*(T.expect [x s]-a)) from by
      dsimp [y]; ring, add_mul]
  refine (norm_add_le ..).trans (add_le_add hb ((norm_add_le ..).trans ?_))
  rw [norm_mul,norm_mul]; exact add_le_add (mul_le_mul_of_nonneg_left (han k i c t) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (han k i c s) (norm_nonneg _))
end YM.Push.Common
