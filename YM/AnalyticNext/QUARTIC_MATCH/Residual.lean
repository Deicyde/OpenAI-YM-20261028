import YM.AnalyticNext.QUARTIC_MATCH.Ward
import YM.Next.FOUNDATIONS.LinkBounds
import YM.Work.F02


/-!
# Separately closed first unmatched tensors

Finite PERIOD at this point. Will need all meshes before making curvature lift.
No nonlinear Ward identity claimed just from closure of this projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch
open Function Filter Matrix Lattice RG Exterior Tree Precision Wilson Bid Tensor
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

section
variable {E X V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Nonlinear substitution into a residue at its first unmatched order. -/
theorem first_comp {k : ℕ} {F : E → X} (hf : ContDiffAt ℝ k F 0)
    (hk : ∀ i < k, iteratedFDeriv ℝ i F 0 = 0)
    {Q : V → E} (hq : ContDiffAt ℝ k Q 0) (he : Q 0=0) :
    iteratedFDeriv ℝ k (F ∘ Q) 0 =
      (iteratedFDeriv ℝ k F 0).compContinuousLinearMap (fun _ => fderiv ℝ Q 0) := by
  let L := fderiv ℝ Q 0
  trans iteratedFDeriv ℝ k (F ∘ L) 0
  · have h : (↑k : WithTop ℕ∞) ≤ ↑k := le_rfl
    have hu : ContDiffAt ℝ k F (Q 0) := he.symm ▸ hf
    rw [iteratedFDeriv_comp hu hq h, iteratedFDeriv_comp (show ContDiffAt ℝ k F (L 0) from (map_zero L).symm ▸ hf)
      L.contDiff.contDiffAt h, he,map_zero]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [FormalMultilinearSeries.compAlongOrderedFinpartition,ftaylorSeries]
    rcases lt_or_eq_of_le c.length_le with hp|hp
    · ext1 v; simp [hk _ hp]
    have heq : Fintype.card ((i : Fin c.length) × Fin (c.partSize i))=k := by
      rw [Fintype.card_congr c.equivSigma,Fintype.card_fin]
    simp only [Fintype.card_sigma,Fintype.card_fin] at heq
    have ha (i) : c.partSize i=1 := by
      have hx := c.partSize_pos i; by_contra! H
      have hy : ∑ _i : Fin c.length, (1 : ℕ) < ∑ i : Fin c.length, c.partSize i :=
        Finset.sum_lt_sum (fun i _ => c.partSize_pos i) ⟨i,Finset.mem_univ _,by omega⟩
      simp [heq,hp] at hy
    have hd : iteratedFDeriv ℝ 1 Q 0 = iteratedFDeriv ℝ 1 L 0 := by
      ext1 v; rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply,L.fderiv]
    simp_rw [show (fun i : Fin c.length => iteratedFDeriv ℝ (c.partSize i) Q 0) =
        (fun i => iteratedFDeriv ℝ (c.partSize i) L 0) from funext fun i => (ha i).symm ▸ hd]
  exact Next.Foundations.jets_linear L hf
end

namespace Residual
open Joint

variable {c f : Side} {S : StepData c f} {G : Gauge}

/-- Finite-period first-unmatched tensor obligations, also used at Wilson top. -/
structure Legal {j : ℕ} (A : T (Dir G c) ℝ j) : Prop where
  ward (l : Fin j) (u : LieSpin G c) (v : Fin j → Dir G c) :
    A (update v l (gradient u)) = 0
  color (t : G.El) (v : Fin j → Dir G c) : A (fun i => colors t (v i)) = A v
  translated (s : Signed) (b : Site c) (v : Fin j → Dir G c) : A (fun i => shifts s b (v i)) = A v
  polar : Tensor.Sym A

lemma gradient_zero : gradient (0 : LieSpin G c)=0 := by funext i; simp [Joint.gradient]
lemma gradient_neg (b : LieSpin G c) : gradient (-b)=-gradient b := by funext i; simp [Joint.gradient]; abel

/-- Closure from actual symmetries and FULL exact equality of all lower jets. -/
theorem inaugurate {F : Dir G c → ℝ} {j : ℕ} (hf : ContDiffAt ℝ j F 0)
    (hs : ∀ i < j, iteratedFDeriv ℝ i F 0=0)
    (hG : F ∘ adjust =ᶠ[𝓝 0] F ∘ Prod.fst) (hC : ∀ t : G.El, F ∘ colors t =ᶠ[𝓝 0] F)
    (hS : ∀ (s : Signed) (b : Site c), F ∘ shifts s b =ᶠ[𝓝 0] F) : Legal (Tensor.coeff F j 0) := by
  have he (L : Dir G c →L[ℝ] Dir G c) (h : F ∘ L =ᶠ[𝓝 0] F) (v : Fin j → Dir G c) :
      Tensor.coeff F j 0 (fun i => L (v i)) = Tensor.coeff F j 0 v := by
    have hh := (h.iteratedFDeriv ℝ j).eq_of_nhds
    rw [Next.Foundations.jets_linear L hf] at hh; simp only [Tensor.coeff,_root_.smul_apply]
    exact congr_arg ((Nat.factorial j : ℝ)⁻¹ • ·) (DFunLike.congr_fun hh v)
  refine ⟨?_, fun i v => he _ (hC i) v, fun s i v => he _ (hS s i) v,Tensor.coeff_symm hf⟩
  intro l u v
  let E := Dir G c × LieSpin G c
  let V : Fin j → E := Function.update (fun i => (v i,0)) l (0,-u)
  let L := ContinuousLinearMap.fst ℝ (Dir G c) (LieSpin G c)
  have ht : F ∘ adjust =ᶠ[𝓝 0] F ∘ L := hG
  have hA := (ht.iteratedFDeriv ℝ j).eq_of_nhds
  rw [Next.Foundations.jets_linear L hf, first_comp hf hs (adjust_analytic.of_le le_top) adjust_zero] at hA
  have he : iteratedFDeriv ℝ j F 0 (fun i => fderiv ℝ adjust 0 (V i))=
      iteratedFDeriv ℝ j F 0 (fun i => L (V i)) := DFunLike.congr_fun hA V
  have hx : (fun i => fderiv ℝ adjust 0 (V i))=update v l (gradient u) := by
    funext i
    by_cases h : i=l
    · rw [h,adjust_rate]; simp [V,gradient_neg]
    rw [adjust_rate]; simp [V,h,gradient_zero]
  have hv : (fun i => L (V i))=Function.update v l 0 := by
    funext i; by_cases h : i=l <;> simp [V,L,h]
  rw [hx,hv,(iteratedFDeriv ℝ j F 0).map_coord_zero l (Function.update_self ..)] at he
  rw [Tensor.coeff, _root_.smul_apply, he,smul_zero]

def baseAt (p : Clip) (R : PathData G) (a : Dir G c) := mainTerm p R (represent a)
variable {R : PathData G} {z A K : ℝ} {q : Clip}

lemma base_ward (hb : R.Bounds q z A K) :
    baseAt (c:=c) q R ∘ adjust =ᶠ[𝓝 0] baseAt q R ∘ Prod.fst := by
  filter_upwards [adjusted] with x hx
  simp only [Function.comp_apply,baseAt,hx,Work.F05.mainTerm_gauge hb]
lemma base_colors (hb : R.Bounds q z A K) (t : G.El) :
    baseAt (c:=c) q R ∘ colors t = baseAt q R := by
  funext x; exact (congr_arg (mainTerm q R) (rep_colors t x)).trans (Work.F05.mainTerm_gauge hb _ _)
lemma base_orient (q : Clip) (R : PathData G) (s : Signed) (b : Site c) :
    baseAt q R ∘ shifts s b = baseAt q R := by funext x; simp [baseAt,rep_shifts,main_pull]
lemma base_smooth (hb : R.Bounds q z A K) : ContDiffAt ℝ ω (baseAt (c:=c) q R) 0 :=
    Work.F02.mainTerm_contDiffAt hb (fun i => (Work.F03.represent_smooth i).contDiffAt)

section diff
variable {W : PathData G} {p : Clip} {M : Bed} {T : Forest S.ratio} {u : Dir G c → AxisChart G T}
  {η σ C Λ : ℝ}

/-- Ordinary per-period closure; exact lower order equality charged explicitly.
Use in particular with lower action carrying cubic path completion (not just its
linearized atom!), EXACT degree-3 match as input. `StationaryScenes` produces through 2. -/
theorem closed (t : S.Choices) {j : ℕ} (h : S.patch.Branches S.kernel G) (hW : W.Bounds p σ C Λ)
    (hp : Critical T p W u) (hc : Comptroller T M p W) (hR : R.Bounds q z A K)
    (he : 0 < η) (hm : PriceGap T p W η)
    (hl : ∀ k<j, iteratedFDeriv ℝ k (value T t p W u) 0=iteratedFDeriv ℝ k (baseAt (c:=c) q R) 0) :
    Legal (Tensor.coeff (value T t p W u - baseAt q R) j 0) := by
  let F := value T t p W u
  let J := baseAt (c:=c) q R
  have hb := SliceExchange.on_shell t hp
  have hj : ContDiffAt ℝ ω F 0 := hb.action.comp 0 hb.arc_smooth
  have hq : ContDiffAt ℝ ω J 0 := base_smooth hR
  apply inaugurate ((hj.sub hq).of_le le_top) (fun i hi => ?_)
  · exact (gauge_value h hW hp hc he hm t).sub (base_ward hR)
  · exact fun y => (color_value h hW hp hc he hm _ _).sub (EventuallyEq.of_eq (base_colors hR y))
  · exact fun s b => (oriented h hW hp hc he hm s b t).sub (EventuallyEq.of_eq (base_orient q R s b))
  change iteratedFDeriv ℝ i (F-J) 0=0
  rw [iteratedFDeriv_sub_apply (hj.of_le le_top) (hq.of_le le_top),show iteratedFDeriv ℝ i F 0=_ from hl i hi,sub_self]
end diff

def wilsonAt (a : Dir G c) : ℝ := Wilson.energy (represent a)

/-- Also at top, SAME Wilson normalization. -/
theorem closed_peak (j : ℕ) (hb : R.Bounds q z A K) (hL : ∀ i<j,
    iteratedFDeriv ℝ i (wilsonAt (c:=c) (G:=G)) 0=iteratedFDeriv ℝ i (baseAt (c:=c) q R) 0) :
    Legal (Tensor.coeff (wilsonAt - baseAt (c:=c) q R) j 0) := by
  have hx := base_smooth (c:=c) hb
  have hf : ContDiffAt ℝ ω (wilsonAt (G:=G) (c:=c)) 0 := by
    unfold wilsonAt Wilson.energy
    exact ContDiffAt.sum fun i _ => Work.F03.price_smooth (A:=fun x => faceValue (represent x) i) (Push.writes ..)
  apply inaugurate ((hf.sub hx).of_le le_top) (fun i hi => ?_)
  · filter_upwards [base_ward (c:=c) hb, adjusted (c:=c) (G:=G)] with x hx hz
    exact congr_arg₂ (· - ·) (show Wilson.energy _ = _ from (congr_arg Wilson.energy hz).trans (Wilson.energy_gauge _ _)) hx
  · intro t
    filter_upwards with x
    exact congr_arg₂ (· - ·) ((congr_arg Wilson.energy (rep_colors t x)).trans (Wilson.energy_gauge ..))
      (congr_fun (base_colors hb t) x)
  · intro s b
    filter_upwards with x; exact congr_arg₂ (· - ·) ((congr_arg Wilson.energy (rep_shifts s b x)).trans
      (Wilson.energy_pull ..)) (congr_fun (base_orient q R s b) x)
  change iteratedFDeriv ℝ i (wilsonAt - baseAt (c:=c) q R) 0=0
  rw [iteratedFDeriv_sub_apply (hf.of_le le_top) (hx.of_le le_top), hL i hi,sub_self]

end Residual
end YM.AnalyticNext.QuarticMatch
