import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Arcus

/-!
# Pack numerical stencils; allow forward/back sweep, both actual types

Brush costs asymmetric if M cuff, portal reserves fixed post-L through degree.
Use on physical V or smooth variation, no clipping assumptions. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Tube Pressure.Stores Work.E03 Exterior Wilson Push.AbsoluteSums Finset
open Precision Shell Channel Next.Fluctuations Bloch Laurent SliceRows.DataKernel
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable {E α β : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {U : E → Config G c} {v u d e η w : ℝ} {k : ℕ}
open Brush
variable {M R Z W : ℕ} {T : Tube G S}
variable [Fintype α] [Fintype β] {A : α→ Site c} {B : β→Site c} {F : Config G c→α→β→Pay G}

structure Pigment (U : E→Config G c) (K c' : ℝ) (x : E) (B : ℕ) (a : α→ Site c) (b : β→Site c)
    (F : Config G c→α→β→Pay G) (X Y k : ℕ) : Prop where
  site : Census X a
  well : Census Y b
  color : Rule B F a b
  budget : 0 ≤ K
  pos : 0≤ c'
  shapes : ∀ {u v : ℝ} (i : α) (j : β) {P : E→ G.Color}, Brush k u v P x → ∀ f : Bool,
    Brush k (K*u) (c'+v) (fun y=> receive (F (U y) i j) f (P y)) x
namespace Pigment
variable (p : Pigment U w d x R A B F Z W k)
include p

lemma pigment_zip {g : E→β→G.Color} (i : α) (hu : 0≤u) (hv : 0≤v) (h : ∀ j, separation (A i) (B j) ≤ R →
    Brush k u v (fun x=> g x j) x) : Brush k (↑(Animals.ballCost R)*W*(w*u)) (d+v) (fun t=> zip (F (U t)) (g t) i) x := by
  refine lifted p.well (add_nonneg p.pos hv) (mul_nonneg p.budget hu) (fun j he=> (p.shapes i j (h j he) true : _))
    (fun i' f he=> p.color.reach (U f) _ _ fun h=> he ?_)
  rw [h, _root_.zero_apply]
lemma pigment_unzip {g : E→α→G.Color} (i : β) (hu : 0≤u) (hv : 0≤v) (h : ∀ j,separation (B i) (A j) ≤ R →
    Brush k u v (fun x=> g x j) x) : Brush k (↑(Animals.ballCost R)*Z*(w*u)) (d+v) (fun t=> unzip (F (U t)) (g t) i) x := by
  refine lifted p.site (add_nonneg p.pos hv) (mul_nonneg p.budget hu) (fun j he=> (p.shapes j i (h j he) false : _)) ?_
  intro j f he; rw [separation_comm]; refine p.color.reach (U f) _ _ (fun ha=> he ?_); change (F (U f) j i).adjoint (g f j)=0; simp [ha]
end Pigment

namespace Strokes
variable (P : Teller G)


def typesL (P : Teller G) := |P.C| *royalty G^2

def coversMark (L : Side) : ℕ := L.val^4*Fintype.card PlaqAxes*Fintype.card Bool+ Fintype.card Axis+Fintype.card Gain

def GradeData (U : E → Config G c) (L : Side) (T : Tube G S) (x : E) (B : ℕ) (d : ℝ) (j : ℕ) :=
    let t := coversMark L; let w:=typesL P; let v:=2*(B:ℝ)*d*royalty G; let a: Twin c→Site c :=fun i=>i.1.1
    Pigment U w v x B (fun i=> S.ratio.parent i.1.1) a (T.Φ B) t t j ∧
    Pigment U w v x B Prod.fst a (T.Φ' B) t t j ∧ Pigment U w v x B Prod.fst a (T.N B) t t j

lemma pigments (R : ℕ) (hP : P.Funds S T) (hd : 0 ≤ d) (hp : ∀ i, Brush k (royalty G) d (fun j=> G.mat (U j i)) x) :
    GradeData P U S.patch.L T x R d k := by
  let L:= S.patch.L; let w:=typesL P; let A : Twin c→Site c :=fun i=>i.1.1
  let q:=coversMark L; let z:=2*(R:ℝ)*d*royalty G; have hR := royalty_ge G
  obtain ⟨hk,hi,hH,-⟩:= hP.crosses
  have he : Census q A := by
    have hx : Census (1*Fintype.card PlaqAxes*Fintype.card Bool) A := Census.withType _
      (Census.withType _ (Census.ordinary (c:=c)))
    intro H; apply (hx H).trans; apply Nat.mul_le_mul_left; unfold q coversMark
    have hy : 1 ≤ L.val^4 := one_le_pow₀ L.property
    exact ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hy))).trans (by omega)
  have hu : Census q (Prod.fst : Bond c→ Site c) := by
    have hx : Census (1*Fintype.card Axis) (Prod.fst : Bond c→Site c) := Census.withType _ Census.ordinary
    intro H; apply (hx H).trans; apply Nat.mul_le_mul_left; unfold q coversMark; omega
  have hv : Census q (Prod.fst : Co c Gain → Site c) := by
    have hx : Census (1*Fintype.card Gain) (Prod.fst : Co c Gain→Site c) := Census.withType _ Census.ordinary
    intro H; apply (hx H).trans; apply Nat.mul_le_mul_left; unfold q coversMark; omega
  have hT : Census q (fun i:Twin f=>S.ratio.parent i.1.1) := by
    have hx : Census (L.val^4*Fintype.card PlaqAxes*Fintype.card Bool) (fun i:Twin f=>S.ratio.parent i.1.1) :=
      Census.withType _ (Census.withType _ (Census.homeland S))
    intro H; apply (hx H).trans; apply Nat.mul_le_mul_left; unfold q coversMark; omega
  have hw : 0≤w := by unfold w typesL; positivity
  have hz : 0≤z := by unfold z; positivity
  have hd' {v C} (hc : C≤|P.C|) (hv : 0≤v) : C*(royalty G^2*v) ≤ w*v := by unfold w typesL; rw [mul_assoc]; gcongr
  refine ⟨⟨hT,he,crosses R T P hP,hw,hz,?_⟩,
    ⟨hu,he,sameLevel R L.val L.property T.R.mn (Row.rights _ _ hk P.width.le) pole mesh,hw,hz,?_⟩,
    ⟨hv,he,sameLevel R L.val L.property T.R.o (Row.rights _ _ hi P.width.le) id mesh,hw,hz,?_⟩⟩
  · intro u v i j K h face; refine (trains i j face h hH P.width.le hd hp R).climb (hd' ?_ h.nonneg) le_rfl
    have hl : 1 ≤ (S.patch.L.val:ℝ)^2 := one_le_pow₀ (by exact_mod_cast L.property)
    apply (div_le_div_of_nonneg_right (le_abs_self _) (sq_nonneg _)).trans; exact div_le_self (abs_nonneg _) hl
  · intro u v i j K h face; exact (relay (pole i) (mesh j) face L.property h hk P.width.le hd hp R).climb (hd' (le_abs_self _) h.nonneg) le_rfl
  intro u v i j K h face; exact (relay i (mesh j) face L.property h hi P.width.le hd hp R).climb (hd' (le_abs_self _) h.nonneg) le_rfl
end Strokes
end YM.ConnectedActivityE6.Blaze
