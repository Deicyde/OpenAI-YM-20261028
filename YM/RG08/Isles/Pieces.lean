import YM.RG08.Isles.Survey

noncomputable section
namespace YM.RG08.Isles
open Forms Pert.Bulk Packets Laurent Finset Function Lattice Filter
open scoped Topology BigOperators ENNReal Classical
set_option autoImplicit false
variable {I:Type} {n:ℕ}{σ C:ℝ}{F:Flake n (Market I)}{f:ViewDeck n I}

lemma decay {a d e:ℝ}{t:ℝ}(h:|t| *Real.exp (σ*d)≤C)(hs:0≤σ)(hc:0≤C)(he:e≤a+d): |t|≤ C*Real.exp (σ*a)*Real.exp (-σ*e):=by
 rw [← mul_le_mul_iff_left₀ (Real.exp_pos (σ*d))]
 refine h.trans ?_
 rw [mul_assoc (C*_),mul_assoc C, ←Real.exp_add,←Real.exp_add]
 exact le_mul_of_one_le_right hc (Real.one_le_exp (by nlinarith))

lemma Study.basis (h:Study σ C f F)(m:ℕ)(x:Tape n (colony I m))(y:Market I)(i j:Fin n)(hi:x i=port (chain m) y):
 |f m x| ≤ C*Real.exp (σ*abroad y)*Real.exp (-σ * native (x j)) := by
 apply decay ((h.calm m).check h.cost (Fin.pos i) x) h.rate.le h.cost
 have he:= region (x j) (x i)
 have hz:(shore (chain m) I).span (x j) (x i) ≤ (shore (chain m) I).radius x:=(shore (chain m) I).le_radius x j i
 have hf:native (x i)≤abroad y:=by rw [hi];exact native_port _
 linarith

lemma Study.two (h:Study σ C f F)(m:ℕ)(x:Tape n (colony I m))(y:Market I)(i j k:Fin n)(hi:x i=port (chain m) y):
 |f m x| ≤ C*Real.exp (σ*abroad y)*weightU (σ/2) (reach (x j))*weightU (σ/2) (reach (x k)):=by
 unfold weightU;rw [mul_assoc (C*_ : ℝ),←Real.exp_add,here,here]
 rw [show -(σ/2)*native (x j)+-(σ/2)*native (x k)= -σ*((native (x j)+native (x k))/2) by ring]
 apply decay ((h.calm m).check h.cost (Fin.pos i) x) h.rate.le h.cost
 have hf:native (x i)≤abroad y:=by rw [hi];exact native_port _
 have he:= region (x j) (x i);have he':=region (x k) (x i)
 linarith [(shore (chain m) I).le_radius x j i,(shore (chain m) I).le_radius x k i]

structure StudyLine (σ C:ℝ)(g:(i:ℕ)→Line (colony I i))(Γ:Line (Market I)) : Prop where
 rate : 0<σ
 palm : Wire (carpet I) σ C Γ
 calm i : Wire (shore (chain i) I) σ C (g i)
 light (x y:Market I): Tendsto (fun i=>g i (port (chain i) x) (port (chain i) y)) atTop (𝓝 (Γ x y))

variable {g:(i:ℕ)→Line (colony I i)} {Γ:Line (Market I)}
lemma StudyLine.turn (h:StudyLine σ C g Γ):StudyLine σ C (fun i=>swap (g i)) (swap Γ):=⟨h.rate,h.palm.turn,fun i=>(h.calm i).turn,fun x y=>h.light y x⟩
lemma StudyLine.point (h:StudyLine σ C g Γ)(m:ℕ)(x y:colony I m):|g m x y| ≤ C*Real.exp (-σ*(shore (chain m) I).span x y):=by
 convert decay (d:=(shore (chain m) I).span x y) (e:=(shore (chain m) I).span x y) (a:=0) ((ENNReal.ofReal_le_ofReal_iff h.palm.gain).mp ((h.calm m).toll x y)) h.rate.le h.palm.gain (by simp) using 1;simp

variable [Fintype I]
omit [Fintype I] in
lemma Study.internal {F:Flake (n+2) (Market I)} {f:ViewDeck (n+2) I}{B:ℝ}(h:Study σ C f F)(H:StudyLine σ B g Γ)(m:ℕ)(x:Tape n (Market I))(i:Fin n)(u:colony I m × colony I m):
   ‖lam (g m) (f m) ((carpetRoad I).visit m ∘ x) u‖ ≤ B*(C*Real.exp (σ*abroad (x i)))*(weightU (σ/2) (reach u.1) * weightU (σ/2) (reach u.2)):=by
 unfold lam;rw [Real.norm_eq_abs,abs_mul,mul_comm]
 apply le_trans (c:=_) (b:=B*(C*Real.exp (σ*abroad (x i))*weightU (σ/2) (reach (P:=chain m) (I:=I) u.1)*weightU (σ/2) (reach (P:=chain m) (I:=I) u.2))) ?_ (le_of_eq (by ring))
 apply mul_le_mul ((H.calm m).plain ..) ?_ (abs_nonneg _) H.palm.gain
 exact h.two m _ (x i) i.succ.succ 0 (Fin.succ 0) (by simp [carpetRoad])

lemma Study.trace {F:Flake (n+2) (Market I)}{f:ViewDeck (n+2) I}{B:ℝ}(h:Study σ C f F)(H:StudyLine σ B g Γ):
 Study σ (C*B) (fun m=>Forms.lap (g m) (f m)) (Forms.lap Γ F):=by
 unfold Forms.lap; apply Study.bleach;refine ⟨h.rate,mul_nonneg h.cost H.palm.gain,h.palm.run H.palm,fun m=> (h.calm m).run (H.calm m),?_⟩
 intro hn x
 let i:Fin n:=⟨0,hn⟩
 let T:= B*(C*Real.exp (σ * abroad (x i)))
 apply DCT ((carpetRoad I).prod (carpetRoad I)) (fun m u=> lam (g m) (f m) ((carpetRoad I).visit m ∘ x) u) (lam Γ F x) (fun u=>T*(weightU (σ/2) u.1 * weightU (σ/2) u.2))
 · intro u; unfold lam;apply Tendsto.mul _ (H.light _ _)
   let y:Tape (n+2) _:=Fin.cons u.1 (Fin.cons u.2 x)
   convert h.light (by omega) y using 2
   congr 2;ext j:1;cases j using Fin.cases with
   | zero=>rfl
   | succ j=>cases j using Fin.cases <;> rfl
 · exact (weightU_twice (by have he:=h.rate;linarith)).mul_left _
 · intro u;unfold T weightU;have he:=h.cost;have hh:=H.palm.gain;positivity
 exact .of_forall fun m u=>h.internal H m x i u

end YM.RG08.Isles
