import Mathlib.Analysis.Calculus.BumpFunction.Normed
import YM.Euclid.Pairing



/-!
# Smooth on Conf with strict positive-time smeared RP gives actual Gram
-/
set_option autoImplicit false
noncomputable section
namespace YM.Table.Pairing
open Function Set Filter MeasureTheory Metric Word
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius ComplexOrder
variable {G : Gauge} {L : Register G} {n : ℕ} {S : Table L} {a : Axis}

lemma nearGram (H : S.Symmetric) (hv : S.Smooth) {p q : L.Word} (hp : Positive p a) (hq : Positive q a) :
    ContinuousAt (fun x : Points p.length × Points q.length => S.gram a (realize (tokens p) x.1) (realize (tokens q) x.2))
      (positions p,positions q) := by
  -- In sufficiently small neighborhood of these points, equal smoothly via displacement
  have hx : single (positions p) a := ⟨hp.1,fun i => hp.2 _ (List.get_mem ..)⟩
  have hy : single (positions q) a := ⟨hq.1,fun i => hq.2 _ (List.get_mem ..)⟩
  let t := (positions p,positions q)
  let C := (pairIso a (n := p.length) (m := q.length)).symm
  let V := tied (tokens p) (tokens q) a
  have he : ContinuousAt (fun x => S.read (C x) V) t := ((S.smooth_read hv V).continuousOn (C t) (spans hx hy)).continuousAt
    ((conf_open _).mem_nhds (spans hx hy)) |>.comp C.continuous.continuousAt
  refine he.congr ?_
  have hA {n} (p : Points n) (h : single p a) : {x : Points n|single x a} ∈ 𝓝 p := by
    refine Eventually.and ((conf_open n).mem_nhds h.1) ?_
    exact eventually_all.mpr (fun i => (show Continuous (fun p : Points n => p i a) from by fun_prop).continuousAt.preimage_mem_nhds (lt_mem_nhds (h.2 i)))
  filter_upwards [show {x : Points p.length×Points q.length | single x.1 a ∧ single x.2 a} ∈ 𝓝 t from
    mem_nhds_prod_iff.mpr ⟨_,hA _ hx,_,hA _ hy, fun _ hh => hh⟩] with z hz
  exact (displacement S H _ _ hz.1 hz.2).symm

structure Bulb {n : ℕ} (x : Points n) (a : Axis) where
  bump : ContDiffBump x
  active : ∀ y∈tsupport bump, single y a

namespace Bulb
variable {x : Points n} (B : Bulb x a)
def r (y : Points n) := B.bump.normed volume y
def f (y : Points n) : ℂ := ↑(B.r y)

lemma controls : tsupport B.f=Metric.closedBall x B.bump.rOut := by
  unfold tsupport; rw [show support B.f=support B.bump from by ext y; simpa [r,f,← B.bump.support_eq] using
    (congr_arg (fun t : Set _ => y∈t) (B.bump.support_normed_eq (μ := volume)) |>.to_iff), ← tsupport,B.bump.tsupport_eq]

lemma controlled : ∀ y ∈ tsupport B.f, single y a := by rw [B.controls,← B.bump.tsupport_eq]; exact B.active

def tests (v : Fin n → L.Token) : PastTest L a where
  n := n
  v := v
  f := ⟨B.f, Complex.ofRealCLM.contDiff.comp B.bump.contDiff_normed,
    (show HasCompactSupport B.f from (show IsCompact (tsupport B.f) from B.controls.symm ▸ isCompact_closedBall _ _)),
    fun y hy => (B.controlled y hy).1⟩
  past y hy := (B.controlled y hy).2

lemma available (u : L.Word) (h : Positive u a) : ∃ B : ℕ → Bulb (positions u) a,
    Tendsto (fun i => (B i).bump.rOut) atTop (𝓝 0) := by
  let x := positions u
  have ht : {x : Points u.length|single x a} ∈ 𝓝 x := Eventually.and ((conf_open _).mem_nhds (show x∈_ from h.1))
    (eventually_all.mpr (fun i => (show Continuous (fun x : Points u.length => x i a) from by fun_prop).continuousAt.preimage_mem_nhds (lt_mem_nhds (show _ from h.2 (u.get i) (List.get_mem ..)))))
  obtain ⟨r,hr,hh⟩ := Metric.mem_nhds_iff.mp ht
  let H (i : ℕ) := r/((i:ℝ)+2)
  have hp i : 0<H i := by unfold H; positivity
  let B (i : ℕ) : ContDiffBump x := ⟨H i/2,H i,by specialize hp i; positivity,by specialize hp i; linarith⟩
  have he i : H i < r := by
    unfold H; rw [div_lt_iff₀ (by positivity)]; nlinarith [Nat.cast_nonneg (α := ℝ) i]
  refine ⟨fun i => ⟨B i, by rw [(B i).tsupport_eq]; exact fun y hy => hh (closedBall_subset_ball (he i) hy)⟩, ?_⟩
  exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
end Bulb

private theorem kernel (H : S.Symmetric) (hv : S.Smooth) {p q : L.Word} (hp : Positive p a) (hq : Positive q a)
    {B : ℕ → Bulb (positions p) a} {J : ℕ → Bulb (positions q) a}
    (he : Tendsto (fun i => (B i).bump.rOut) atTop (𝓝 0)) (hd : Tendsto (fun i => (J i).bump.rOut) atTop (𝓝 0)) :
    Tendsto (fun i => ∫ x, S.smeared a ((B i).tests (tokens p)) ((J i).tests (tokens q)) x) atTop (𝓝 (S.gram a p q)) := by
  let x := positions p
  let y := positions q
  let X := Points p.length × Points q.length
  let v (i : ℕ) (p : X) := (B i).r p.1 * (J i).r p.2
  let F (r : Points p.length × Points q.length) := S.gram a (realize (tokens p) r.1) (realize (tokens q) r.2)
  let R := F (x,y)
  have hR : R=S.gram a p q := by simp [R,F,x,y]
  have hs i : ∀ z, S.smeared a ((B i).tests (tokens p)) ((J i).tests (tokens q)) z = v i z • F z := by
    intro z
    change star (↑((B i).r z.1) : ℂ) * ↑((J i).r z.2) * _ = _
    simp [v,F,Bulb.tests,Complex.real_smul]
  rw [← hR]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨r,hr,ht⟩ := Metric.continuousAt_iff.mp (nearGram H hv hp hq) (ε/2) (by linarith)
  filter_upwards [he.eventually (gt_mem_nhds hr),hd.eventually (gt_mem_nhds hr)] with i h h'
  let T := (B i).tests (tokens p)
  let V := (J i).tests (tokens q)
  change dist (∫ z, S.smeared a T V z) R<ε
  have hS (z : X) : S.smeared a T V z=v i z • F z := hs i z
  have hB : Integrable (v i : X → ℝ) volume := (B i).bump.integrable_normed.mul_prod (J i).bump.integrable_normed
  have ht' : ∫ z, v i z=1 := by
    change (∫ z, v i z ∂(_ : Measure (Points p.length × Points q.length)))=_
    calc
      _ = (∫ z, (B i).r z) * (∫ z, (J i).r z) := integral_prod_mul ..
      _ = _ := by unfold Bulb.r; rw [(B i).bump.integral_normed,(J i).bump.integral_normed,mul_one]
  have hz (s : X) : 0 ≤ v i s := mul_nonneg ((B i).bump.nonneg_normed _) ((J i).bump.nonneg_normed _)
  rw [dist_eq_norm]
  let P := fun z : X => S.smeared a T V z
  change ‖(∫ z, P z) - R‖ < ε
  have hh : Integrable P := pairedIntegrable S H hv T V
  calc
    _ = ‖∫ z, (P z - v i z • R)‖ := by rw [integral_sub hh  (hB.smul_const _), integral_smul_const, ht',one_smul]
    _ ≤ ∫ z, ‖P z - v i z • R‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z : X, v i z * (ε/2) := by
      apply integral_mono (hh.sub (hB.smul_const R)).norm (hB.mul_const _)
      intro z; change ‖P z - v i z • R‖ ≤ v i z * (ε / 2); rw [show P z=_ from hS z,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (hz z)]
      by_cases he:v i z=0
      · rw [he,zero_mul,zero_mul]
      have hp := (mul_ne_zero_iff.mp he).1; have hq := (mul_ne_zero_iff.mp he).2
      have ha : dist z (x,y)<r := by
        rw [Prod.dist_eq]; apply max_lt
        · apply lt_of_lt_of_le _ (le_of_lt h)
          exact mem_ball.mp ((B i).bump.support_normed_eq (μ := volume) ▸ hp)
        apply lt_of_lt_of_le _ (le_of_lt h')
        exact mem_ball.mp ((J i).bump.support_normed_eq (μ := volume) ▸ hq)
      exact mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact (ht ha).le) (hz z)
    _ < ε := by rw [integral_mul_const,ht',one_mul]; linarith

lemma at_point (H : S.Symmetric) (hv : S.Smooth) (h : S.RPSmear) : S.RP := by
  intro a m v ht c
  choose B he using fun i => Bulb.available (v i) (ht i)
  let P (j i) := (B i j).tests (tokens (v i))
  have hh i k : Tendsto (fun j => ∫ x, S.smeared a (P j i) (P j k) x) atTop (𝓝 (S.gram a (v i) (v k))) := kernel H hv (ht i) (ht k) (he i) (he k)
  exact ge_of_tendsto (tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun k _ => (hh i k).const_mul _))) (Eventually.of_forall fun i => h.2 a m (P i) c)
end YM.Table.Pairing
