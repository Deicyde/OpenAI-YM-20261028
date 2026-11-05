import YM.Push.LOOP_COEFFICIENT.Carries
import YM.Push.LOOP_COEFFICIENT.Paths.Calculus
import YM.Push.LOOP_COEFFICIENT.Vertex

/-!
# Ordered two-through-four translation jets as a Hessian vertex
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Paths
open Function Filter Set Matrix Lattice Laurent Bloch Exterior RG Complex Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {a b J E ι : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype J] [DecidableEq J] [Fintype E] [DecidableEq E]
    {n : Side}

abbrev Roll (a : Type) (k : ℕ) [Fintype a] := CSpace a [×k]→L[ℂ] ℂ

def consume (k : ℕ) : Roll a (2+k) → (Fin k → CSpace a) → Roll a 2 :=
  match k with
  | 0 => fun f _ => f
  | n+1 => fun f v => consume n (f.curryLeft (v 0)) (Fin.tail v)

omit [DecidableEq a] in
lemma consume_value {k : ℕ} (f : Roll a (2+k)) (v : Fin k → CSpace a) (u : Fin 2 → CSpace a) : consume k f v u = f (prepend u v) := by
  induction k with
  | zero => rfl
  | succ n ih => simp only [consume,ih, ContinuousMultilinearMap.curryLeft_apply,prepend]

def tailLin (f : Roll a 2) := LinearMap.mk₂ ℂ (fun x y => f ![x,y])
  (fun x y _ => f.cons_add _ x y) (fun t x _ => f.cons_smul _ t x)
  (fun x y w => (f.curryLeft x).cons_add _ y w) (fun t x y => (f.curryLeft x).cons_smul _ t y)

def formMap (N : Matrix a b ℂ) : Roll a 2 →ₗ[ℂ] Matrix b b ℂ := {
  toFun f := of fun i j => f ![N.col i, N.col j]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl }
omit [DecidableEq a] in
lemma form_pair (N : Matrix a b ℂ) (f : Roll a 2) (x y) : x ⬝ᵥ (formMap N f *ᵥ y) = f ![N *ᵥ x, N *ᵥ y] := by
  let A := (tailLin f).compl₁₂ N.mulVecLin N.mulVecLin
  have he : formMap N f = LinearMap.toMatrix₂' ℂ A := by ext i j; rw [LinearMap.toMatrix₂'_apply]; change _ = f ![N *ᵥ _, N *ᵥ _]; rw [Matrix.mulVec_single_one,Matrix.mulVec_single_one]; rfl
  rw [he, ← Matrix.toLinearMap₂'_apply']; change ((LinearMap.toMatrix₂' ℂ).symm ((LinearMap.toMatrix₂' ℂ) A) x y : ℂ) = _
  rw [LinearEquiv.symm_apply_apply]; rfl

def splitVertex (N P : Matrix a b ℂ) (f : (k : ℕ) → (Fin k → Momentum) → Roll a k) : Vertex b b b where
  base q := formMap N (f 2 ![-q,q])
  one q p := ((formMap N).comp (f 3 ![p,-(q+p),q]).curryLeft.toLinearMap).comp P.mulVecLin
  two q p s := (((LinearMap.mk₂ ℂ (fun v w => ((f 4 ![p,s,-(q+p+s),q]).curryLeft v).curryLeft w)
    (by intros; ext; simp [ContinuousMultilinearMap.curryLeft_apply]) (by intros; ext; simp [ContinuousMultilinearMap.curryLeft_apply]) (by intros; simp) (by intros; simp)).compr₂ (formMap N)).compl₁₂ P.mulVecLin P.mulVecLin)

def bank (N P : Matrix E J ℝ) (g : (E → ℝ) → ℝ) (b : J → ℝ) := bilinearAt (fun a => g (P *ᵥ b + N *ᵥ a)) 0

variable {N P : Matrix E J ℝ} {g : (E → ℝ) → ℝ} {f : CSpace E → ℂ}
omit [DecidableEq E] in
lemma bank_smooth (hg : ContDiffAt ℝ ω g 0) : ContDiffAt ℝ ω (bank N P g) 0 := matrix_diff fun i j => by
  simp only [bank,bilinearAt_apply]; exact mixed_smooth (clm N) (clm P) hg ..

variable (hg : ContDiffAt ℝ ω g 0) (he : ContDiffAt ℂ ω f 0) (hf : ∀ᶠ x in 𝓝 0, (g x : ℂ) = f (cvec x))
include hg he hf
def vecCLM : (E → ℝ) →L[ℝ] CSpace E := ContinuousLinearMap.pi fun i => ofRealCLM.comp (ContinuousLinearMap.proj i)

omit [DecidableEq E] in
lemma bank_test {k : ℕ} (v : Fin k → (J → ℝ)) i j :
    (((iteratedFDeriv ℝ k (bank N P g) 0 v) i j : ℝ) : ℂ) = iteratedFDeriv ℂ (2+k) f 0 (prepend ![(cmat N).col i, (cmat N).col j] fun l => cmat P *ᵥ cvec (v l)) := by
  let A := ((Matrix.entryLinearMap ℝ ℝ i j : Matrix J J ℝ →ₗ[ℝ] ℝ)).toContinuousLinearMap
  have h := A.iteratedFDeriv_comp_left (bank_smooth (N:=N) (P:=P) hg) (le_top (a:=(k:WithTop ℕ∞))) (x:=0)
  change Complex.ofReal (A (iteratedFDeriv ℝ k (bank N P g) 0 v)) = _
  change iteratedFDeriv ℝ k (fun b => A (bank N P g b)) 0 = _ at h
  rw [show (fun b => A (bank N P g b)) = fun b => iteratedFDeriv ℝ 2 (fun a => g (clm P b + clm N a)) 0 ![Pi.single i 1, Pi.single j 1] from funext fun b => bilinearAt_apply ..] at h
  rw [show A (iteratedFDeriv ℝ k (bank N P g) 0 v) = _ from (DFunLike.congr_fun h v).symm, mixed_partial _ _ hg, show ∀ v : Fin (2+k) → E → ℝ, Complex.ofReal (iteratedFDeriv ℝ (2+k) g 0 v) = iteratedFDeriv ℂ (2+k) f 0 (fun i => cvec (v i)) from real_slots (vecCLM (E:=E)) ofRealCLM he hg hf]
  congr 1
  have ht : ∀ (k) (w : Fin 2 → (E → ℝ)) (z : Fin k → (E → ℝ)), (fun i => cvec (prepend w z i)) = prepend (fun i => cvec (w i)) (fun i => cvec (z i)) := by
    intro n; induction n with
    | zero => intros; rfl
    | succ n ih => intro w z; funext l; refine Fin.cases rfl (fun i => congr_fun (ih w (Fin.tail z)) i) l
  rw [ht]; congr 1
  · ext1 l; fin_cases l <;> simp [clm] <;> rfl
  · ext1 l; exact (cmat_mulVec _ _).symm

omit [DecidableEq E] in
lemma bank_base (x y : CSpace J) : x ⬝ᵥ ((actualMatrix (bank N P g)).base *ᵥ y) = iteratedFDeriv ℂ 2 f 0 ![cmat N *ᵥ x, cmat N *ᵥ y] := by
  convert form_pair (cmat N) (iteratedFDeriv ℂ 2 f 0) x y using 3
  ext i j; simpa only [prepend,iteratedFDeriv_zero_apply,Nat.add_zero] using! bank_test (N:=N) (P:=P) hg he hf (![]) i j
omit [DecidableEq E] in
lemma bank_one (x y v : CSpace J) : x ⬝ᵥ ((actualMatrix (bank N P g)).lin v *ᵥ y) = iteratedFDeriv ℂ 3 f 0 ![cmat P *ᵥ v, cmat N *ᵥ x, cmat N *ᵥ y] := by
  have h := complex_ext (L:=(actualMatrix (bank N P g)).lin) (T:=((formMap (cmat N)).comp (iteratedFDeriv ℂ 3 f 0).curryLeft.toLinearMap).comp (cmat P).mulVecLin) fun w => by
    ext i j; rw [actualMatrix,actual_real₁]; simpa only [iteratedFDeriv_one_apply, prepend, Matrix.cons_val_zero] using! bank_test (N:=N) (P:=P) hg he hf ![w] i j
  rw [h]; apply form_pair (cmat N) ((iteratedFDeriv ℂ 3 f 0).curryLeft _) x y
omit [DecidableEq E] in
lemma bank_two (x y v w : CSpace J) : x ⬝ᵥ ((actualMatrix (bank N P g)).quad v w *ᵥ y) = iteratedFDeriv ℂ 4 f 0 ![cmat P *ᵥ v, cmat P *ᵥ w,cmat N *ᵥ x, cmat N *ᵥ y] := by
  let V := splitVertex (cmat N) (cmat P) fun k _ => iteratedFDeriv ℂ k f 0
  have he := complex_ext₂ (L:=(actualMatrix (bank N P g)).quad) (T:=V.two 0 0 0) fun v w => by
    ext i j; rw [actualMatrix,actual_real₂]; simpa only [iteratedFDeriv_two_apply, prepend,Fin.tail_cons, Matrix.cons_val_zero] using! bank_test (N:=N) (P:=P) hg he hf ![v,w] i j
  rw [he]; apply form_pair (cmat N) (((iteratedFDeriv ℂ 4 f 0).curryLeft _).curryLeft _) x y
end YM.Push.Loops.Paths
