import YM.RG08.Germ.Squares
import YM.PertExtension.BareChart

/-! # Relative Haar log at non-tree

Separable adapter to the actual LocalRatio (same Haar at each fine Period).
For bulk propagation stamp all links; restriction with tree log=0 must receive
the *non-tree* values at prescribed path coordinates, not an extra constant.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Work.F08 Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix Tree
open PertExtension.Chart
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius InnerProductSpace Classical
variable {c f : Side} (S : StepData c f) {G : Gauge} (T : Forest S.ratio)
variable {P : ChartRatio G} {w : ℝ} {r : ℕ}

lemma logs_trunk {u : Link G f} (h : FreeResolvent.Vanishes T u) (j : ↥T.trunks) :
    arm G f 1 u (j.val.1,coord j.val.2)=0 := by
  ext v; exact h v _ j.property
lemma logs_plain (x : FreeResolvent.Active G T→ℝ) (j : T.Free) :
    arm G f 1 (sprig S T G *ᵥ x) (j.val.1,coord j.val.2)=FreeResolvent.profile T x j := by
  ext v; rw [show arm G f 1 _ _ _= (sprig S T G*ᵥ x) (FreeResolvent.plant T (j,v)) from rfl];
  simp [sprig, Matrix.mulVec,FreeResolvent.insertion, dotProduct,(FreeResolvent.plant_inj T).eq_iff]; rfl
lemma drape_sprig (x : FreeResolvent.Active G T→ℝ) : T.drape (expLinks G _ (FreeResolvent.profile T x))=input G f (sprig S T G *ᵥ x) := by
  funext i; unfold input; rw [Work.F03.represent_link]; by_cases he : i∈T.trunks
  · exact ((T.on_tree _ ⟨i,he⟩)).trans (Eq.symm <| (congr_arg G.lieExp (logs_trunk _ _ (sprig_in S T x) (⟨i,he⟩:↥T.trunks))).trans (by simp))
  · exact (T.off_tree _ ⟨i,he⟩).trans (Eq.symm <| congr_arg G.lieExp (logs_plain S T x (⟨i,he⟩:T.Free)))

def hatJ (P : ChartRatio G) (x : Link G f) := ∑ i : Body 1 f, Real.log (P.J (arm G f 1 x i))
lemma hat_period (x : FreeResolvent.Active G T→ℝ) (h : LocalRatio P) :
    hatJ P (sprig S T G *ᵥ x)=∑ j : T.Free,Real.log (P.J (FreeResolvent.profile T x j)) := by
  unfold hatJ; rw [← Equiv.sum_comp (Equiv.prodCongr (Equiv.refl _) axisEquiv)];
  symm
  let p (i : Edge (Site f)) := Real.log (P.J (arm G f 1 (sprig S T G*ᵥ x) (i.1,coord i.2)))
  calc
    _ = ∑ i: T.Free, p i.val := sum_congr rfl fun i _=> congr_arg (fun x=>Real.log (P.J x)) (logs_plain S T x i).symm
    _ = ∑ i,p i := by
      calc
        _ = ∑ i ∈ Finset.univ.filter (fun i=> i∉T.trunks),p i := (Finset.sum_subtype (p:=fun i=> i∉T.trunks) _ (fun _=> by simp) p).symm
        _ = _ := Finset.sum_subset (filter_subset ..) (fun i hi hj=> by
          have ha : i∈T.trunks := not_not.mp (fun h=> hj (mem_filter.mpr ⟨hi,h⟩))
          have he := logs_trunk S T (sprig_in S T x) (⟨i,ha⟩ : ↥T.trunks)
          unfold p; rw [show arm G f 1 (sprig S T G *ᵥ x) (i.1,coord i.2)=0 from he]; rw [h.anchored,Real.log_one])
    _ = _ := rfl

private def toneColor (j : TypeFace 1) : Corn (Loc G 1) →L[ℝ] G.Color := LinearMap.toContinuousLinearMap {
  toFun u := WithLp.toLp 2 fun i => u (j,i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl }
private def hatAura (P : ChartRatio G) (x : Corn (Loc G 1)) := ∑ i : TypeFace 1, Real.log (P.J (toneColor i x))
lemma hat_aura (h : LocalRatio P) : AnalyticAt ℝ (hatAura P) 0 := by
  have hv : ContDiffAt ℝ ω P.J 0 := h.germ _ (Metric.mem_ball_self h.patch)
  have hp : ContDiffAt ℝ ω (fun x=> Real.log (P.J x)) 0 := hv.log (h.anchored ▸ one_ne_zero)
  apply (show ContDiffAt ℝ ω _ _ from ContDiffAt.sum (fun i _=> ?_)).analyticAt
  exact (toneColor (G:=G) i|>.map_zero|>.symm ▸ hp).comp _ (toneColor i).contDiff.contDiffAt
lemma hat_reads (P : ChartRatio G) (f : Side) : hatJ (f:=f) P= atmosphere (fun i=> some (0,i)) (hatAura P) f := by
  funext x; unfold hatJ atmosphere; rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; rw [Function.comp_apply,hatAura]; apply sum_congr rfl; intro j _
  congr 2; ext1 z
  change x (i,j,z)= x (i+wrap f 0,j,z); rw [map_zero,add_zero]

def brimJ (u : G.ColorIndex) (P : ChartRatio G) (r : ℕ) := breath (0,coord 0,u) (fun i : Loc G 1=>some (0,i)) (hatAura P) r
lemma brim_good (u : G.ColorIndex) (h : LocalRatio P) (m : Side) (r : ℕ) : AnalyticAt ℝ (hatJ P (f:=m)) 0 ∧
    recital (brimJ u P r) m=Tensor.coeff (hatJ P) r 0 := by
  rw [hat_reads]; exact breath_proofs _ (hat_aura h) _ _ _ _
lemma brim_price (u : G.ColorIndex) (P : ChartRatio G) (h : 0≤w) (r : ℕ) : ∃ C : ℝ,0≤ C ∧ Glow (brimJ u P r) w C := breath_quote _ _ _ w h
lemma brim_tune (u : G.ColorIndex) (P : ChartRatio G) (r : ℕ) : Tunable (brimJ u P r) := breath_tune (ι:=Loc G 1) ..

abbrev hatsScale (K : Forest S.ratio) (P : ChartRatio G) := P.scale^(Fintype.card K.Free)
theorem hats_restore (h : LocalRatio P) : ∀ᶠ x : T.Free → G.Color in 𝓝 0,
    PertExtension.Chart.jacobian P x = hatsScale S T P * Real.exp (hatJ P (sprig S T G*ᵥ FreeResolvent.active T x)) := by
  have hp : ∀ᶠ v:G.Color in 𝓝 0,0<P.J v := by
    filter_upwards [Metric.ball_mem_nhds (0:G.Color) h.patch] with i hi; exact h.pos i hi
  filter_upwards [eventually_all.mpr (fun i : T.Free=>
    (show ContinuousAt (fun z : T.Free→G.Color=>z i) 0 from (continuous_apply _).continuousAt).eventually hp)] with i hi
  rw [hat_period S T _ h,Real.exp_sum,hatsScale,jacobian];
  have hh j : 0 < P.J (FreeResolvent.profile T (FreeResolvent.active T i) j) := hi j
  simp_rw [Real.exp_log (hh _)];
  rw [← show (∏ _j : T.Free,P.scale)=_ from (show (∏ _j : T.Free,P.scale)=P.scale^Fintype.card T.Free from by simp), ← Finset.prod_mul_distrib]; exact prod_congr rfl fun j _=> max_eq_left (mul_pos h.scale (hi j)|>.le)
end YM.RG08
