import YM.RG08.Forms.Lines

/-!
# Cover PDE unary contraction (self Wick pairing in a connected vertex)
-/
noncomputable section
namespace YM.RG08.Forms
open Pert.Bulk Packets Finset Function
open scoped BigOperators Topology ENNReal Classical
set_option autoImplicit false
variable {I : Type}{m:ℕ}

def lam (Γ : Line I) (F : Flake (m+2) I) (x : Tape m I) (u : I×I) := F (Fin.cons u.1 (Fin.cons u.2 x)) * Γ u.1 u.2

def run (Γ : Line I) (F : Flake (m+2) I) : Flake m I:=fun x=>∑' u,lam Γ F x u

def lap (Γ : Line I) (F : Flake (m+2) I) : Flake m I := bleach (run Γ F)

/- include bleach simply to force symmetry independent of input. Real stencil polynomials
see the symmetrization as exact already before integration. -/

variable {d : Ground I} {σ C B : ℝ} {Γ:Line I}{F:Flake (m+2) I}
lemma unary (h : Held d σ C F) (hΓ : Wire d σ B Γ) : Ensign (fun x:Tape m I=> ∑' u:I×I,bill (lam Γ F x u) (σ*d.radius x)) (ENNReal.ofReal (C*B)):=by
 intro i z
 calc
  _ ≤ ∑' x,∑' (u:I×I),row (mark d σ F) i.succ.succ z (Fin.cons u.1 (Fin.cons u.2 x)) * ENNReal.ofReal B:=ENNReal.tsum_le_tsum fun x=>?_
  _ = (∑' w,row (mark d σ F) i.succ.succ z w) * ENNReal.ofReal B:=by
     rw [ENNReal.tsum_comm, ENNReal.tsum_prod',tsum_cons (f:=row (mark d σ F) i.succ.succ z)]
     simp_rw [tsum_cons (p:=m) (f:=fun w=>row (mark d σ F) _ z (Fin.cons _ w)),ENNReal.tsum_mul_right]
  _ ≤ _:=by
     rw [mul_comm C B, ENNReal.ofReal_mul hΓ.gain, mul_comm (ENNReal.ofReal B)]
     exact mul_le_mul_left ((ensign.mp h) _ _) _
 by_cases hz:x i=z
 · simp only [row,hz,Fin.cons_succ,if_true]
   apply ENNReal.tsum_le_tsum; intro u
   unfold lam bill mark
   simp_rw [bill]
   rw [← ENNReal.ofReal_mul (by positivity)]
   refine ENNReal.ofReal_le_ofReal ?_;rw [abs_mul,mul_right_comm _ _ (Real.exp _)]
   have he:=d.radius_comp (Fin.cons u.1 (Fin.cons u.2 x):Tape (m+2) I) (fun i:Fin m=>i.succ.succ)
   have hw : d.radius x≤ d.radius (Fin.cons u.1 (Fin.cons u.2 x)):=by
     convert he; ext i;simp
   have hb:=hΓ.plain u.1 u.2
   have hs := hΓ.width
   gcongr
 · simp [row,hz,Fin.cons_succ]

/- At arity zero the sum does not have absolute convergence (vacuum scalar volume).
Do not use real tsum value in that case on cover. -/
lemma unary_sum (h : Held d σ C F) (hΓ : Wire d σ B Γ) (hm : 0<m) (x : Tape m I) : Summable (fun u=> ‖lam Γ F x u‖) := by
 have he := bill_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((unary h hΓ).point hm x))
 have hh: Real.exp (σ*d.radius x)≠0:=Real.exp_ne_zero _
 refine (he.mul_right ((Real.exp (σ*d.radius x))⁻¹)).congr ?_
 intro i
 simp [Real.norm_eq_abs,hh]

lemma Held.run (h : Held d σ C F) (hΓ : Wire d σ B Γ) : Held d σ (C*B) (Forms.run Γ F):= ensign.mpr ((unary h hΓ).mono (fun _=>bill_tsum _ _) le_rfl)
lemma Held.lap (h : Held d σ C F) (hΓ : Wire d σ B Γ) (hC:0≤C) : Held d σ (C*B) (Forms.lap Γ F):= (h.run hΓ).bleach (mul_nonneg hC hΓ.gain)

lemma run_compare (hm : 0<m) {F' : Flake (m+2) I} {Γ':Line I} {σ' C' B' B₀ σ₁:ℝ} (hF':Held d σ' C' F')(hfΓ:Wire d σ' B' Γ)(hΓ':Wire d σ' B₀ Γ') (h : Held d σ₁ C F)(hk : Wire d σ₁ B Γ):
    run Γ F - run Γ' F' = run Γ (F-F') + run (Γ-Γ') F':=by
 funext x
 have hr:= (unary_sum h hk hm x).of_norm
 have h' := (unary_sum hF' hfΓ hm x).of_norm
 have h0:= (unary_sum hF' hΓ' hm x).of_norm
 have hd : lam Γ (F-F') x=lam Γ F x - lam Γ F' x:=by ext i; simp only [lam,Pi.sub_apply,sub_mul]
 have he : lam (Γ-Γ') F' x=lam Γ F' x - lam Γ' F' x:=by ext i; simp only [lam,Pi.sub_apply,mul_sub]
 simp only [Pi.sub_apply,Pi.add_apply,Forms.run,hd,he]
 change (∑' _,_) - (∑' _,_)=(∑' i,(lam Γ F x i-lam Γ F' x i))+∑' i,(lam Γ F' x i-lam Γ' F' x i)
 rw [hr.tsum_sub h',h'.tsum_sub h0];ring

lemma lap_compare (hm : 0<m) {F' : Flake (m+2) I} {Γ':Line I} {C' B' : ℝ} (h : Held d σ C F)(h': Held d σ C' F') (hk:Wire d σ B Γ)(hk':Wire d σ B' Γ'):
    lap Γ F - lap Γ' F' = lap Γ (F-F') + lap (Γ-Γ') F' := by
 unfold lap
 -- simplify run_compare signature
 rw [← bleach_sub, ← bleach_add]
 congr 1
 -- pass dummy Δ assumptions? remove unused
 exact run_compare hm h' hk hk' h hk

end YM.RG08.Forms
