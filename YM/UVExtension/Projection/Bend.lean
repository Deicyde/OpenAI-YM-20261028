import YM.UVExtension.Projection.Ripple
import YM.UVExtension.Projection.Query.Test
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Fixed pre-L interpolation receipt. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Projection
open Lattice RG Precision Tree Exterior Bloch Laurent Wilson Stationary Filter Function Finset
open scoped Matrix Topology BigOperators ContDiff Classical
variable {G : Gauge} {P : Rates G}
def armada:= Set.Icc (0:ℝ) 1
abbrev Team:=↥armada
def rower (x:Team):ℝ:=x.1
def dash (d : ℕ)(j:Fin (d+1)):Team:=⟨ j.val/((d:ℝ)+1), div_nonneg (by positivity) (by positivity), by rw [div_le_one (by positivity)]; exact_mod_cast j.isLt.le⟩
lemma dash_inj (d:ℕ): Injective (rower ∘ dash d):=by
  intro i j he; apply Fin.ext
  change ((i.val:ℝ)/_)=j.val/((d:ℝ)+1) at he
  exact_mod_cast (div_left_inj' (show (d:ℝ)+1≠0 by positivity)).mp he
open Polynomial

def shutter (d : ℕ) (j:Fin (d+1)) := (Lagrange.basis univ (rower ∘ dash d) j)
def measureB (d : ℕ) (t:Team) (j: Fin (d+1)):= (shutter d j).eval (rower t)
lemma clicked {d : ℕ}{f : Team→ℝ} (h : (Projection.straight rower).pace d f) (v:Team) : f v = ∑ j,measureB d v j *f (dash d j):=by
  obtain ⟨Q,hQ,h⟩:=h
  have hh : Q.degree < ↑(@univ (Fin (d+1)) _).card := by
    simp only [card_univ,Fintype.card_fin,Nat.cast_withBot]; exact Q.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le hQ))
  have he:=Lagrange.eq_interpolate (dash_inj d|>.injOn) hh
  simp only [h]; conv => lhs; rw [he,Lagrange.interpolate_apply,eval_finsetSum]
  simp [measureB,shutter,mul_comm]
  -- backup
lemma phase_bend (h : Toned P)(B:Bed)(p : G.ColorIndex)(d : ℕ)(z:Team)(U:Team→Cube G×ℝ)(f:Team→Head P)(g:Team→Stamp P)(he:∀ i,Aligns P B (U i) (f i) (g i))(hp: Keyline P B) (hh : ∀ i j v,(Projection.straight rower).pace d fun n=> f n i j v)(hx:∀ i v,(Projection.straight rower).pace d fun n=> g n i v): U z= ∑ i,measureB d z i • U (dash d i):=by
  apply Aligns.unicity (he z) _ p h hp
  have hf : f z= ∑ j,measureB d z j • f (dash d j):= by funext i k v; simp_rw [Finset.sum_apply]; exact clicked (hh i k v) z
  have hg : g z= ∑ j,measureB d z j • g (dash d j):= by funext i v; simp_rw [Finset.sum_apply]; exact clicked (hx i v) z
  rw [hf,hg]; exact Aligns.join P B _ _ _ _ (fun i _=> (he _).scale _)

lemma confirms (d : ℕ)(j:Fin (d+1)): ∃ K:ℝ,0 ≤ K ∧ ∀ x y, ‖measureB d y j - measureB d x j‖ ≤ K*‖rower y-rower x‖:=by
  let f:=shutter d j
  let g:=fun i:ℝ=> f.derivative.eval i
  have h: Continuous g:= f.derivative.continuous
  obtain ⟨K,h⟩:= ((isCompact_Icc (α:=ℝ) (a:=0) (b:=1)).image h).isBounded.exists_norm_le
  refine ⟨max 0 K,le_max_left .., fun x y=>?_⟩
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s:=armada) (f:=fun i=> f.eval i) (f':=g) _ _ _ x.property y.property
  · exact fun i hi=> (f.hasDerivAt _).hasDerivWithinAt
  · exact fun i hi=> (h _ ⟨i,hi,rfl⟩).trans (le_max_right ..)
  exact convex_Icc ..

structure Ahead (d:ℕ)(ε:ℝ): Prop where
    pos : 0<ε
    small : 4*ε≤1
    paid (X: Type) [NormedAddCommGroup X] [NormedSpace ℝ X](U:Team→ X) : (∀ z,U z=∑ i,measureB d z i • U (dash d i)) → (∀ z, ‖U z‖≤ ε) → ∀ x y, ‖U x-U y‖ ≤ (1/4:ℝ)*‖rower x-rower y‖
lemma pick (d : ℕ): ∃ ε:ℝ,Ahead d ε:=by
  choose C hC h using fun i=> confirms d i
  let a:= ∑ j, C j
  have ha:0 ≤ a:= sum_nonneg fun i _=> hC i
  let b:= (1/4:ℝ)/(1+a); have hb:0<b:=by unfold b; positivity
  have hx : b*(1+a)=1/4:= div_mul_cancel₀ _ (by linarith)
  have hv : b*a ≤ 1/4:= hx ▸ mul_le_mul_of_nonneg_left (by linarith) hb.le
  refine ⟨b,hb,by nlinarith,fun X _ _ U hu hr x y=>?_⟩
  have hf: U x - U y=∑ i,(measureB d x i-measureB d y i) • U (dash d i):= by simp_rw [sub_smul, sum_sub_distrib,← hu]
  rw [hf]; let w:= ‖rower x-rower y‖
  refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun i=> C i*w*b) fun i _ => ?_).trans ?_)
  · rw [norm_smul]; exact mul_le_mul (h i y x) (hr _) (norm_nonneg _) (mul_nonneg (hC _) (norm_nonneg _))
  rw [← sum_mul, ← sum_mul,mul_right_comm]; exact mul_le_mul_of_nonneg_right ((mul_comm _ b).trans_le hv) (norm_nonneg _)
end YM.UVExtension.Projection
