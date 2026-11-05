import YM.Next.RANK.Radian.Differ

/-! heat removed away from the diagonal. Elementary off-zero Spire calculus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Radian
open MeasureTheory Filter Maxwell Topology Analysis Asymptotics Set Real Metric Beamer Lattice 
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal FourierTransform RealInnerProductSpace
local notation "𝑒" => Real.exp
local notation "ℑ" => Complex.I

variable {G : Gauge} {x : E4} {n : ℕ}
variable {f g v w u : E4 → ℝ} {s t b : ℝ}

-- Laurent-like functions, only away from diagonal. heat drive propagates through pols.

abbrev spike (x : E4) := (‖x‖^2)⁻¹
def pin (x : Axis) : E4→ℝ:= fun y=> y x
inductive Spire : (E4 →ℝ) → Prop
| hill : Spire spike
| ascend (a) : Spire (pin a)
| rope (f : ℝ) : Spire (fun _=>f)
| product : {f g : E4→ℝ}→ Spire f → Spire g → Spire (f*g)
| ridge : {f g : E4→ℝ}→ Spire f → Spire g→ Spire (f+g)
| close : {f g : E4→ℝ}→ Spire f → EqOn f g away → Spire g
lemma outside_eq {X : Type*} (a b : E4→X) (h : EqOn a b away) (he : x∈away): a=ᶠ[𝓝 x] b:= (show ∀ᶠ v in 𝓝 x,v∈away from open_away.mem_nhds he).mono fun _ hi=> h hi
lemma Spire.smooth (h : Spire f) (he : x≠0): ContDiffAt ℝ ∞ f x:= by
  induction h
  · exact (contDiff_norm_sq ℝ).contDiffAt.inv (by dsimp; have hv : ‖x‖≠0 := norm_ne_zero_iff.mpr he;positivity)
  · unfold pin;fun_prop
  · exact contDiffAt_const
  · apply ContDiffAt.mul <;> assumption
  · apply ContDiffAt.add <;> assumption
  rename_i F H f hx hh; exact hh.congr_of_eventuallyEq (outside_eq F H hx he).symm
lemma Spire.charge (h : Spire f) : ∃ (q : ℝ) (i : ℕ), 0≤ q ∧ ∀ z : E4, 1 ≤ ‖z‖ → ‖f z‖≤ q *‖z‖^i:= by
  induction h with
  | hill=>
    refine ⟨1,0,zero_le_one,fun z hz=>?_⟩
    unfold spike;rw [Real.norm_of_nonneg (by positivity), pow_zero,mul_one]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hz)
  | ascend a=>
    exact ⟨1,1,zero_le_one,fun z hz=> by rw [pin, Real.norm_eq_abs,← basis_inner,pow_one, ← show ‖basis a‖=1 from basis_norm ..]; exact abs_real_inner_le_norm _ _⟩
  | rope c=>exact ⟨‖c‖,0,norm_nonneg _,fun i _=>by simp⟩
  | product h hb ih hv=>
    obtain ⟨c,i,hc,ho⟩:=ih; obtain ⟨b,j,hb',hy⟩:=hv
    refine ⟨c*b,i+j,by positivity,fun i h=>?_⟩;rw [Pi.mul_apply,norm_mul]; exact (mul_le_mul (ho i h) (hy i h) (norm_nonneg _) (by positivity)).trans (by rw [mul_mul_mul_comm,pow_add])
  | ridge h hb ih hv=>
    obtain ⟨c,i,hc,ho⟩:=ih; obtain ⟨b,j,hb',hy⟩:=hv
    refine ⟨c+b,i+j,by positivity,fun x hx=>?_⟩;rw [Pi.add_apply,add_mul];exact (norm_add_le ..).trans ((add_le_add (ho x hx) (hy x hx)).trans (add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (by omega)) hc) (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (by omega)) hb')))
  | close h hh I=>
    obtain ⟨c,i,hc,H⟩:=I; exact ⟨c,i,hc,fun x hx=>by rw [← hh];exact H x hx;exact norm_pos_iff.mp (zero_lt_one.trans_le hx)⟩
lemma spike_grad (hx : x≠0) (a) : grad a spike x= -2*x a *spike x^2:= by
  have he:= first_Green hx a
  have hf : fderiv ℝ Green x = Maxwell.normal • fderiv ℝ spike x:= (fderiv_const_mul (𝕜:=ℝ) (b:=Maxwell.normal) ((Spire.smooth .hill hx).differentiableAt (by simp)))
  unfold grad D at *; rw [hf] at he; change Maxwell.normal*_ = _ at he; apply mul_left_cancel₀ Maxwell.normal_pos.ne'; exact he.trans (by unfold spike;ring)
lemma Spire.more (H : Spire f) (a : Axis): Spire (grad a f):= by
  induction H with
  | rope c=> exact Spire.close (.rope 0) (fun y hy=>by simp [grad,D])
  | hill=>exact Spire.close (((Spire.rope (-2)).product (.ascend a)).product ((Spire.hill).product .hill)) (fun z hz=> by simpa [pin,pow_two] using (spike_grad hz a).symm)
  | ascend i=>
    apply Spire.close (.rope (basis a i))
    intro x hx;change _= fderiv ℝ (compAxis i) x _; rw [(compAxis i).hasFDerivAt.fderiv];rfl
  | @ridge f g h hv ih hg =>
    exact Spire.close (ih.ridge hg) (fun x hx=> by
      change _= fderiv ℝ (f+g) x _;rw [fderiv_add ((h.smooth hx).differentiableAt (by simp)) ((hv.smooth hx).differentiableAt (by simp))]; rfl)
  | @product f g h hv ih hg=>
    exact Spire.close ((h.product hg).ridge (hv.product ih)) (fun x hx=> by
      change _= fderiv ℝ (f*g) x _;rw [fderiv_mul ((h.smooth hx).differentiableAt (by simp)) ((hv.smooth hx).differentiableAt (by simp))]; rfl)
  | close h hh I=> exact I.close (fun x hx=> GermD _ (outside_eq _ _ hh hx))

lemma burn_grad (b) (i : Axis) (x : E4) : grad i (blaze b) x= blaze b x*((-b*2)*x i):= by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (-b)).exp
  change fderiv ℝ (fun x : E4=> 𝑒 (-b * ‖x‖^2)) x (basis i)=_
  rw [h.fderiv]; unfold blaze;simp only [smul_apply]; simp [two_smul]; rw [← real_inner_comm x,basis_inner];ring
lemma sparks (H : Spire f) (a : Axis) : ∃ g,Spire g ∧ EqOn (grad a (f*blaze b)) (g*blaze b) away:= by
  let g:=grad a f; let p:= fun (x:E4) => ((-b*2)*x a)
  have hp : Spire p:= (Spire.rope (-b*2)).product (.ascend a)
  refine ⟨g+f*p,(H.more a).ridge (H.product hp),fun x hx=> ?_⟩
  have hh : ContDiff ℝ ∞ (blaze b):= Real.contDiff_exp.comp ((contDiff_const.mul (contDiff_norm_sq ℝ)))
  change fderiv ℝ (f*blaze b) x _=_; rw [fderiv_mul ((H.smooth hx).differentiableAt (by simp)) (hh.differentiable (by simp) x)]
  change f x*grad a (blaze b) x+ blaze b x*g x=(g x+ f x*p x)*blaze b x; rw [burn_grad];unfold p;ring
lemma longev (f : E4→ℝ) (h : Spire f) (t : ℝ) (s : List Axis) : ∃ g, Spire g∧EqOn (dV s (f*blaze t)) (g*blaze t) away:= by
  induction s with
  | nil=>exact ⟨f,h,fun x _=>rfl⟩
  | cons a l I=>
    obtain ⟨g,hv,hH⟩:=I; obtain ⟨p,he,hx⟩:= sparks (b:=t) hv a
    exact ⟨_,he,fun x hx'=> Eq.trans (GermD _ (outside_eq _ _ hH hx')) (hx hx')⟩
lemma faded (h : Spire f) (hp : 0 < t) (s : List Axis) (D : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E4, 1 ≤ ‖z‖ → ‖z‖^D* ‖dV s (f*blaze t) z‖ ≤ C:= by
  obtain ⟨g,he,hh⟩:= longev f h t s; obtain ⟨C,k,hC,hK⟩:= he.charge
  obtain ⟨p,hp',hv⟩:= warmth (k+D) t hp
  refine ⟨C*p,by positivity,fun z hz=>?_⟩
  rw [hh (show z∈away from norm_pos_iff.mp (zero_lt_one.trans_le hz)), Pi.mul_apply,norm_mul,Real.norm_of_nonneg (r:=blaze t z) (by unfold blaze; positivity)]
  apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hK z hz) (show 0≤blaze t z from (Real.exp_pos _).le)) (pow_nonneg (norm_nonneg _) _))
  have ht : 𝑒 (-(t/2)*‖z‖^2)≤1:= Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hp]) (sq_nonneg _))
  have he := (hv z).trans (mul_le_of_le_one_right (by linarith only [hp']) ht); rw [pow_add] at he
  unfold blaze; linarith only [mul_le_mul_of_nonneg_left he hC]
end YM.Next.Rank.Radian
