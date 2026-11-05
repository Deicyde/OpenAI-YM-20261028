import Mathlib.Data.Set.Finite.List
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hood
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Suites

/-!
# Uniform analytic budgeting for param integrability. NOT volume-uniform

 Choose Λ(Y) after period here. Used only for domination to justify the
 equations. Pointwise Utopia's Hit budget much finer. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function MeasureTheory
open scoped Topology InnerProductSpace ContDiff BigOperators Classical
variable {E F G Y T A B ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup G] [NormedSpace ℝ G]
open Brush
variable {k : ℕ} {x:E}

/-- Post-period hypothesis used only for exchanging integrals. Existence
 of constant within family independently of hard Y input, not Stamina.
 Excludes φ-far state if V look there not qualified in U. -/
structure Zest (f : A → E→F) (x:E) (k:ℕ) : Prop where
  post : ∃ C,0≤C ∧ ∀ᶠ y in 𝓝 x, ∀ a, Brush k C 1 (f a) y

namespace Zest
variable {f g : A → E→F} (hf : Zest f x k)
include hf
lemma congr (h : ∀ᶠ i in 𝓝 x, ∀ a,f a i=g a i) : Zest g x k := by
  obtain ⟨C,hC,hp⟩:=hf.post; refine ⟨C,hC,?_⟩
  filter_upwards [hp,eventually_eventually_nhds.mpr h] with y hy hb a; exact
    (hy a).shimmy (hb.mono fun i hi=> (hi a).symm)
lemma via (p : T→A) : Zest (fun t=> f (p t)) x k :=
    ⟨by obtain ⟨C,hC,hp⟩:= hf.post; exact ⟨C,hC,hp.mono fun y hy t=> hy _⟩⟩
lemma emigrate {p:F→Y} {S : Set F} (h : IsCompact S) (hp : ∀ y∈S, ContDiffAt ℝ (↑k) p y) (hS : ∀ᶠ y in 𝓝 x, ∀ a,f a y∈ S) :
    Zest (fun a y=>p (f a y)) x k := by
  obtain ⟨C,hC,h₁⟩:= Brush.compact h hp; obtain ⟨w,hw,H⟩:= hf.post
  refine ⟨k.factorial*C*(1+(1+w))^k,by positivity,?_⟩
  filter_upwards [H,hS] with i hi h a
  simpa only [mul_one] using! ((hi a).pine (h₁ _ (h _))).trim

lemma wand [FiniteDimensional ℝ F] {p:F→Y} (hp : ContDiff ℝ (↑k) p) : Zest (fun a y=>p (f a y)) x k := by
  obtain ⟨C,hC,H⟩:= hf.post
  exact hf.emigrate (isCompact_closedBall 0 C) (fun _ _=>hp.contDiffAt) (H.mono fun x h a=> mem_closedBall_zero_iff.mpr (h a).bound)
lemma pair {g : A→E→Y} (p : Zest g x k) : Zest (fun a i=> (f a i,g a i)) x k := by
  obtain ⟨C,hC,H⟩:=hf.post; obtain ⟨W,hW,hF⟩:=p.post; refine ⟨(C+W)+(C+W),by positivity,?_⟩
  filter_upwards [H,hF] with y hy hv a; exact Brush.pair ((hy a).climb (by linarith) le_rfl) ((hv a).climb (by linarith) le_rfl)
lemma together (p : Zest g x k) : Zest (fun a y=> f a y+g a y) x k := by
  obtain ⟨C,hC,H⟩:=hf.post; obtain ⟨W,hW,hF⟩:=p.post; exact ⟨C+W, add_nonneg hC hW, (H.and hF).mono fun i hi a=> (hi.1 a).gathering (hi.2 a)⟩
lemma against : Zest (fun a i=> -(f a i)) x k := by
  obtain ⟨C,hC,H⟩:=hf.post; exact ⟨C,hC,H.mono fun i hi a=> (hi a).opposite⟩
lemma plusminus (p : Zest g x k) : Zest (fun a i=> f a i-g a i) x k := by simp only [sub_eq_add_neg]; exact hf.together p.against
lemma replay (L : F→L[ℝ] Y) : Zest (fun a y=> L (f a y)) x k := by
  obtain ⟨C,hC,H⟩:=hf.post; exact ⟨‖L‖*C,by positivity,H.mono fun i hi a=> (hi a).report L le_rfl⟩
lemma scalar (d : ℝ) : Zest (fun a i=> d • f a i) x k := by obtain ⟨C,hC,H⟩:=hf.post; exact ⟨‖d‖*C,by positivity,H.mono fun i hi a=>
    (hi a).smul d⟩
omit hf
lemma single {f:E→F} (h : ContDiffAt ℝ (↑k) f x) : Zest (fun (_:A)=>f) x k := by
  obtain ⟨C,hC,hp⟩:=Brush.neighborhood x h; exact ⟨C,hC.le,hp.mono fun i hi _=> hi⟩
lemma parallel {f:A→F} {w:ℝ} (hw : 0≤w) (h : ∀ i, ‖f i‖≤w) : Zest (fun i (_:E)=>f i) x k :=
    ⟨w,hw,Eventually.of_forall fun _x i=> (Brush.certified zero_le_one _).climb (h i) le_rfl⟩
lemma still (u:F) : Zest (fun (_:A) (_:E)=>u) x k := single contDiffAt_const
lemma paint {f g : A→E→ℝ} (h : Zest f x k) (p : Zest g x k) : Zest (fun i y=> f i y*g i y) x k :=
    (h.pair p).wand (p:=fun z:ℝ×ℝ=>z.1*z.2) (by fun_prop)
lemma total (s : Finset ι) (f : ι→ A→E→ F) (hf : ∀ i∈s, Zest (f i) x k) : Zest (fun i y=>∑ j∈s,f j i y) x k := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using! (still (x:=x) (k:=k) (0:F))
  | insert i s hi hh => simp_rw [Finset.sum_insert hi]; exact (hf i (Finset.mem_insert_self ..)).together
                            (hh fun j hj=> hf _ (Finset.mem_insert_of_mem hj))
lemma full (s : Finset ι) (f : ι→ A→E→ ℝ) (hf : ∀ i∈s, Zest (f i) x k) : Zest (fun i y=>∏ j∈s,f j i y) x k := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using! (still (x:=x) (k:=k) (1:ℝ))
  | insert i s hi hh => simp_rw [Finset.prod_insert hi]; exact (hf i (Finset.mem_insert_self ..)).paint
                            (hh fun j hj=> hf _ (Finset.mem_insert_of_mem hj))
lemma folds [Fintype ι] {f:A→ E→ι→F} (h : ∀ j, Zest (fun i y=> f i y j) x k) : Zest f x k := by
  choose C hC H using fun i => (h i).post
  refine ⟨∑ i,C i,Finset.sum_nonneg (fun i _=> hC i),?_⟩
  filter_upwards [eventually_all.mpr H] with i hi a
  exact Brush.fold zero_le_one (Finset.sum_nonneg fun i _=> hC i) (fun j=> (hi j a).climb (Finset.single_le_sum (fun i _=> hC i) (Finset.mem_univ j)) le_rfl)
end Zest
end YM.ConnectedActivityE6.Blaze
