import YM.Next.RANK.BoundParticle
import YM.Next.RANK.Haar
import YM.Next.RANK.LoomNative
import YM.Work.E05



/-! # Log variable control for old axial patches -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Lattice Wilson RG Beamer Function MeasureTheory Set Filter
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side} {b d : ℕ} {o : Site n}

-- uniform constants at no cost in L
structure Rules (G : Gauge) where
  C : ℝ
  c : ℝ
  positive : 0 < C
  radius : 0 < c
  light (x : G.Color) : ‖x‖ ≤ c → G.chord (G.lieExp x) ≤ 2*‖x‖
  records (v : G.El) : G.chord v ≤ c → G.lieExp (G.plog (G.mat v))=v
  sleeve (v : G.El) : G.chord v ≤ c → ‖G.plog (G.mat v)‖ ≤ 2*G.chord v
  bars (v : G.El) : G.chord v ≤ c → ‖G.plog (G.mat v)-G.curvature v‖ ≤ C * G.chord v^2

lemma direct (u : G.El) : G.curvature u = G.projectColor (G.mat u-1) := G.colorMat_injective
    (by rw [G.colorMat_project, Work.E05.curvature_tangent])
lemma charts (G : Gauge) : Nonempty (Rules G) := by
  obtain ⟨P,hP⟩ := (G.exp_jet.contDiffAt (x:=0)).analyticAt
  have he (x : G.Color) : P.partialSum 2 x=1+G.colorMat x := by
    rw [FormalMultilinearSeries.partialSum,Finset.sum_range_succ,Finset.sum_range_one,hP.coeff_zero, Gauge.mat_lieExp_zero,Gauge.mat_one]
    exact congr_arg (1+·) (DFunLike.congr_fun (hP.hasFDerivAt.unique G.expDiff_zero) x)
  obtain ⟨C,hc,H⟩ := (hP.isBigO_sub_partialSum_pow 2).exists_pos
  let D:= C/G.colorScale; have hg := G.colorScale_pos; have hd : 0<D := div_pos hc hg
  have h (x : G.Color) : x-G.curvature (G.lieExp x)=G.projectColor (G.colorMat x - (G.mat (G.lieExp x)-1)) := by
    simp only [direct,map_sub,G.project_colorMat]
  have hA : ∀ᶠ x in 𝓝 (0:G.Color), ‖x-G.curvature (G.lieExp x)‖ ≤ D*‖x‖^2 := by
    filter_upwards [H.bound] with x hx
    rw [h]; apply (G.project_norm _).trans
    rw [norm_sub_rev]
    have hv : ‖G.mat (G.lieExp (0+x))-P.partialSum 2 x‖ ≤ C* ‖(‖x‖^2:ℝ)‖ := hx
    rw [zero_add,he,sub_add_eq_sub_sub,Real.norm_of_nonneg (sq_nonneg _)] at hv
    unfold D; rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right hv hg.le
  have hh : Tendsto (fun x : G.El => G.plog (G.mat x)) (𝓝 1) (𝓝 0) := by
    simpa only [G.mat_one,G.plog_one] using! (G.plog_diff.continuousAt.tendsto.comp (G.continuous_mat.tendsto 1))
  obtain ⟨R,hR,h⟩ := surrounds G _ (G.plog_right.and (hh.eventually (hA.and (metric_law G))))
  obtain ⟨B,hB,H⟩ := Metric.nhds_basis_closedBall.eventually_iff.1 (metric_law G)
  have hs (x) (hx : G.chord x ≤ min R B) : G.lieExp (G.plog (G.mat x))=x ∧ ‖G.plog (G.mat x)‖ ≤ 2*G.chord x ∧
      ‖G.plog (G.mat x) - G.curvature x‖ ≤ (4*D) * G.chord x^2 := by
    obtain ⟨e₁,e₂,e,h⟩ := h (show x ∈ G.shell R from hx.trans (min_le_left ..))
    let z:= G.plog (G.mat x)
    change ‖z-G.curvature _‖ ≤ D*‖z‖^2 at e₂; change ‖z‖/2≤ _ at e
    change G.lieExp z=x at e₁; rw [e₁] at e₂ e
    have ht : ‖z‖ ≤ 2*G.chord x := by linarith only [e]
    refine ⟨e₁,ht,e₂.trans ?_⟩
    calc
      _ ≤ D*(2*G.chord x)^2 := by gcongr
      _ = _ := by ring
  exact ⟨⟨4*D,min R B,by positivity,lt_min hR hB,fun i hi => (H (Metric.mem_closedBall.mpr (show dist i 0 ≤ B by rw [dist_zero_right]; exact hi.trans (min_le_right ..)))).2,
    fun i hi => (hs i hi).1,fun i hi => (hs i hi).2.1,fun i hi => (hs i hi).2.2⟩⟩

lemma weave (u v : G.El) : ‖G.curvature (u*v)-(G.curvature u+G.curvature v)‖ ≤ G.colorScale * G.chord u * G.chord v := by
  rw [direct,direct,direct,← map_add,← map_sub]
  rw [show G.mat (u*v)-1- (G.mat u-1+(G.mat v-1))=(G.mat u-1)*(G.mat v-1) by rw [G.mat_mul]; noncomm_ring]
  calc
    _ ≤ _ := G.project_norm _
    _ ≤ ‖G.mat u-1‖*‖G.mat v-1‖/G.colorScale := div_le_div_of_nonneg_right (norm_mul_le ..) G.colorScale_pos.le
    _ = _ := by
      have hv (i : G.El) : G.chord i=‖G.mat i-1‖/G.colorScale := rfl
      rw [hv,hv]; field_simp [G.colorScale_pos.ne']

def stage (p : Word b) (Y : Turn b → G.Color) := List.sum (p.map fun a => if a.2 then -Y a.1 else Y a.1)
lemma played_cost (p : Word b) {τ : ℝ} (v : Turn b→ G.El) (hp : 0 ≤ τ) (h : ∀ i,G.chord (v i)≤τ) :
    G.chord (played v p) ≤ (p.length:ℝ)*τ ∧ ‖G.curvature (played v p)-stage p (G.curvature∘v)‖ ≤ (p.length:ℝ)^2 * G.colorScale * τ^2 := by
  induction p with
  | nil => simp [played,stage,G.chord_one]
  | cons a p H =>
    let w := if a.2 then (v a.1)⁻¹ else v a.1
    have hw : G.chord w ≤ τ := by unfold w; split; rw [G.chord_inv]; exact h _; exact h _
    have he : played v (a::p)=w*played v p := rfl
    have hs : stage (a::p) (G.curvature∘v) = G.curvature w+ stage p (G.curvature∘v) := by
      simp only [stage,List.map_cons, List.sum_cons]; unfold w; split_ifs; rw [G.curvature_inv]; rfl; rfl
    rw [he, hs, List.length_cons, Nat.cast_add,Nat.cast_one]
    constructor
    · rw [add_mul,one_mul]; exact (G.chord_triangle ..).trans ((add_le_add hw H.1).trans_eq (add_comm ..))
    let x := played v p;let L:= (p.length:ℝ)
    apply (norm_sub_le_norm_sub_add_norm_sub _ (G.curvature w+G.curvature x) _).trans
    rw [add_sub_add_left_eq_sub]; apply (add_le_add (le_trans (weave ..) (mul_le_mul (mul_le_mul_of_nonneg_left hw G.colorScale_pos.le) H.1
      (G.chord_nonneg _) (mul_nonneg G.colorScale_pos.le hp))) H.2).trans
    let c:= G.colorScale * τ^2; have hc : 0≤c := mul_nonneg G.colorScale_pos.le (sq_nonneg _)
    have ht : L+L^2 ≤ (L+1)^2 := by unfold L; nlinarith [Nat.cast_nonneg (α:=ℝ) p.length]
    change _+L^2*_ *_≤ (L+1)^2*_ *_
    linarith only [mul_le_mul_of_nonneg_right ht hc]

-- normalized axial link coordinates. only compare on proper patches.
abbrev Space (G : Gauge) {n : Side} (o : Site n) (b : ℕ) := Dim o b → G.Color

def wired (t : ℝ) (o : Site n) (b) (U : Config G n) : Space G o b := fun x => t⁻¹ • G.plog (G.mat (spine U o x.val))
def rows (t : ℝ) {o : Site n} (h : 2*(b+1)<n.val) (q : Turn b→ G.Color) : Space G o b := fun x => t⁻¹ • stage (word G h x) q

theorem closer (V : Rules G) (h : 2*(b+1)<n.val) (U : Config G n) {τ : ℝ} (hU : Healthy τ (patch b o) U) (t : ℝ) (ht : 0<t)
    (hτ : 0 < τ) (hr : 4*b*τ ≤ V.c) :
    let a := 4*b*τ
    ‖wired t o b U‖ ≤ 2*a/t ∧ (∀ x : Dim o b,G.lieExp (t • wired t o b U x)= spine U o x.val) ∧
      ‖wired t o b U-rows t h (G.curvature ∘ registered b U o)‖ ≤ (V.C+G.colorScale)*a^2/t := by
  intro a; have he:= V.positive
  let D:= G.curvature ∘ registered b U o
  have ha : 0≤a := by unfold a; positivity
  have hs (i : Dim o b) :
      G.chord (spine U o i.val) ≤ a ∧ ‖G.curvature (spine U o i.val)-stage (word G h i) D‖≤ G.colorScale*a^2 := by
    rw [spun _ _ h i]; let l:= word G h i; let v:= registered b U o
    obtain ⟨e₁,e₂⟩ := played_cost l v hτ.le (chords b U τ hU h)
    have hh : ((List.length l):ℝ) ≤ 4*(b:ℝ) := by exact_mod_cast lengths_word G h i
    refine ⟨e₁.trans (mul_le_mul_of_nonneg_right hh hτ.le),e₂.trans (le_trans (show (l.length:ℝ)^2 * _ * _ ≤ (4*(b:ℝ))^2*G.colorScale*τ^2 from ?_) (le_of_eq ?_))⟩
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _); exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hh 2) G.colorScale_pos.le
    unfold a; ring
  have hp := inv_pos.mpr ht
  refine ⟨(pi_norm_le_iff_of_nonneg (show 0 ≤ 2*a/t by positivity)).2 (fun i => ?_), fun i => ?_, (pi_norm_le_iff_of_nonneg (show 0≤(V.C+G.colorScale)*a^2/t by have := G.colorScale_pos; positivity)).2 (fun i => ?_)⟩
  · unfold wired; rw [norm_smul,Real.norm_of_nonneg hp.le,← div_eq_inv_mul]; exact div_le_div_of_nonneg_right ((V.sleeve _ ((hs i).1.trans hr)).trans
      (mul_le_mul_of_nonneg_left (hs i).1 (by norm_num))) ht.le
  · unfold wired; rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul,V.records _ ((hs i).1.trans hr)]
  unfold wired rows; rw [Pi.sub_apply,← smul_sub,norm_smul,Real.norm_of_nonneg hp.le,← div_eq_inv_mul]
  apply div_le_div_of_nonneg_right _ ht.le
  obtain ⟨hB,hY⟩ := hs i
  apply (norm_sub_le_norm_sub_add_norm_sub _ (G.curvature (spine U o i.val)) _).trans
  rw [add_mul]; exact add_le_add ((V.bars _ (hB.trans hr)).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (G.chord_nonneg _) hB _) he.le)) hY
end YM.Next.Rank.Spindle
