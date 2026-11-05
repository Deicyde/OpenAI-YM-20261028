import YM.Next.RANK.Ratios

/-!
# Endpoint W wind from the real array

Suppress even non-tree links by measuring from the axial paths. For *linear*
endpoint propagation it suffices to use curvature of the link itself (after
frame fixing). Then extended exact linear curl, shutter against all continuum
endpoint stencils. Includes linearization error and outside size needed for
weight calculations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function Filter MeasureTheory Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Beamer
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {B : ℕ} {V Ω : Type*} {P : Schedule} {k i : ℕ}
variable (o : Site n) {τ : ℝ} (U : Config G n) (c : ℝ) (V : Fin 0→Unit)

def rho (q : Edge (Site n) → G.Color) (f : Face (Per n)) : G.Color:= let a:=f.2.val.1; let b:=f.2.val.2; let x:=f.1
                                       q (x,a)+q (x+step a,b)-q (x+step b,a)-q (x,b)
def somata (B : ℕ) (x : Edge (Site n)) : G.Color:= if x∈Room o B then c⁻¹ • G.curvature (spine U o x) else 0

def afloat (B : ℕ) : bead G n → ℝ := rigid (rho (somata o U c B))
private def vorticity {M : Type*} [NormedAddCommGroup M] (F : Cover→Axis→ M) (a b : Axis) (z : Cover) := F z a + F (z+step a) b - F (z+step b) a -F z b
private lemma rot {M : Type*} [NormedAddCommGroup M] (F : Cover → Axis → M) (a b c) :
    let H:= vorticity F
    CellsInt.stepValue (H b c) a + CellsInt.stepValue (H c a) b + CellsInt.stepValue (H a b) c=0 := by
  intro H
  let f (i:Axis) z:= F z i
  let L (i:Axis) (v:Cover → M):=CellsInt.stepValue v i
  have hk i j:H i j=L i (f j)-L j (f i):= by funext v; simp only [H,f,L,vorticity,CellsInt.stepValue,Pi.sub_apply]; abel
  have hf i x y:L i (x-y)= L i x-L i y:= by funext z;simp only [L,CellsInt.stepValue,Pi.sub_apply]; abel
  have hh i j x :L i (L j x)=L j (L i x):= by
    funext z; dsimp only [L,CellsInt.stepValue]; rw [add_right_comm z]; abel
  change L a (H b c)+L b (H c a)+L c (H a b)=_
  rw [hk,hk,hk, hf,hf,hf, hh a b, hh a c, hh b c]; abel

private lemma chance_W (V : Edge (Site (P.side k i)) → G.Color): shutter (fun x : Address G=> rigid (rho V) (body (p:=i) (P:=P) (k:=k) 0 x)):= by
  let R:= fun x : Address G => rigid (rho V) (body (p:=i) (P:=P) (k:=k) 0 x)
  let S(z : Cover) (j):= V (wrap _ z,j)
  have he x a b (h : a<b) : Beamer.polar R a b x=vorticity S a b x:= by
    ext k; rw [poll_at R a b x h k]; unfold R body vorticity S; simp only [zero_add,map_add,wrap_step];rfl
  have ht a b : Beamer.polar R a b =vorticity S a b:= by
    funext i; rcases lt_trichotomy a b with h|h|h; exact he _ _ _ h
    · subst b; simp only [polar, lt_self_iff_false,↓reduceDIte]; unfold vorticity; abel
    rw [Beamer.reverse R,Pi.neg_apply,he i b a h]; unfold vorticity; abel
  intro a b c; change CellsInt.stepValue (polar R b c) a + CellsInt.stepValue (polar R c a) b + CellsInt.stepValue (polar R a b) c= _
  rw [ht b c,ht c a,ht a b]; exact rot S a b c
lemma shuttered (B c) (U : Config G (P.side k i)) (o) : shutter (fun x : Address G=> afloat o U c B (body (p:=i) (P:=P) (k:=k) 0 x)):= chance_W _

lemma therm (B) {n : Side} (x : Site n) (y : Face (Per n)) (hu : separation x y.1 + 2 ≤ B) :
    let a:=y.2.val.1; let b:= y.2.val.2; let z:=y.1; let F:= Room x B
    (z,a)∈F ∧ (z+step a,b)∈ F∧ (z,b)∈F∧ (z+step b,a)∈F:= by
  intro a b z F
  have hv (o : Site n) (j:Axis) : separation o (o+step j)≤ 1:= by rw [separation_comm, separation, add_comm, add_sub_cancel_right]; exact pdist_step _
  have he (i : Site n) (j:Axis) (hx : separation x i +1≤B) : (i,j) ∈ F:= mem_filter.mpr ⟨mem_univ _,(doors _).2 (le_trans (Nat.le_succ _) hx),(doors _).2 ((separation_triangle ..).trans ((Nat.add_le_add_left (hv i j) (separation x i)).trans hx))⟩
  have hh i : separation x (z+step i)+1≤B:= by
    have ht : separation x (z+step i) ≤ separation x z+1:= (separation_triangle x z (z+step i)).trans (Nat.add_le_add_left (hv z i) (separation x z))
    exact (Nat.add_le_add_right ht 1).trans hu
  have hi:separation x z+1≤ B:= (Nat.add_le_add_left (by decide : 1 ≤ 2) _).trans hu
  exact ⟨he z a hi,he _ b (hh _),he z b hi, he _ a (hh _)⟩

variable (hu : 2*(B+1)<n.val) (hz : Healthy τ (Spindle.patch B o) U) (hc : 0<c) (ht : 0≤τ)

include hu hz ht
private lemma wing e (he : e∈Room o B) : G.chord (spine U o e) ≤ 4*B*τ:= by
  let x : Dim o B:= ⟨e,he⟩; let v:= word G hu x
  rw [show spine U o e= _ from spun U o hu x]; apply (played_cost v _ ht (chords B U τ hz hu)).1.trans
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast lengths_word G hu x) ht

include hc
lemma stream j : |afloat o U c B j| ≤ 4 * (4*B*τ/c):= by
  let f:= somata o U c B
  have he i: ‖f i‖≤4*B*τ/c:= by
    unfold f somata; split
    · rename_i h
      rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hc|>.le),← div_eq_inv_mul]; exact div_le_div_of_nonneg_right ((G.curvature_norm _).trans (wing o U hu hz ht i h)) hc.le
    rw [norm_zero]; positivity
  let p:= fromBead G j
  refine (rigidHelm (rho f) j).trans ?_
  unfold rho; dsimp only
  apply (norm_sub_le ..).trans; apply le_trans (add_le_add (le_trans (norm_sub_le ..) (add_le_add (le_trans (norm_add_le ..) (add_le_add (he _) (he _))) (he _))) (he _)); exact le_of_eq (by ring)

omit hc hu hz ht in
lemma warp4 {v t w x : G.El} {b : ℝ} (h₁ : G.chord v≤b) (h₂ : G.chord w ≤ b) (h₃ : G.chord t≤ b) (h₄ : G.chord x≤ b):
    ‖G.curvature (v*w*t⁻¹*x⁻¹) -(G.curvature v+G.curvature w-G.curvature t-G.curvature x)‖ ≤ (6*G.colorScale)*b^2:= by
  let s:=G.colorScale; have hx:s>0:= G.colorScale_pos; have h':0≤ b:=(G.chord_nonneg v).trans h₁
  let c:=s*b^2
  have ht(a b : G.El) {z y : ℝ} (hz : G.chord a ≤ z) (hy: G.chord b≤y) : ‖G.curvature (a*b)-(G.curvature a+G.curvature b)‖≤ s*z*y:= (weave ..).trans (mul_le_mul (mul_le_mul_of_nonneg_left hz hx.le) hy (G.chord_nonneg _) (mul_nonneg hx.le ((G.chord_nonneg _).trans hz)))
  have hh u V a (hu : G.chord u ≤ a) (hv : G.chord V≤b) (v : G.Color): ‖G.curvature (u*V⁻¹)-(v-G.curvature V)‖ ≤ s*a*b+ ‖G.curvature u-v‖:= by
    refine (norm_sub_le_norm_sub_add_norm_sub _ (G.curvature u+G.curvature (V⁻¹)) _).trans (add_le_add (ht u _ hu (G.chord_inv V|>.trans_le hv)) ?_); rw [G.curvature_inv]; exact le_of_eq (congr_arg norm (by abel))
  have hp: G.chord (v*w)≤ b+b:=(G.chord_triangle ..).trans (add_le_add h₁ h₂)
  have hχ:G.chord (v*w*t⁻¹)≤ b+b+b:= (G.chord_triangle ..).trans (add_le_add hp ((G.chord_inv t).trans_le h₃))
  refine (hh _ x (b+b+b) hχ h₄ _).trans (le_trans (add_le_add_right ((hh _ t _ hp h₃ _).trans (add_le_add_right (ht _ _ h₁ h₂) _)) _) ?_)
  exact le_of_eq (by unfold s; ring)

lemma competed (j : bead G n) (hj : separation o j.1+2≤ B) :
    |(rigid (kiosk c o U) j) -afloat o U c B j|≤ 6*G.colorScale*(4*B*τ)^2/c := by
  let X:=kiosk c o U; let Y:=rho (somata o U c B)
  let z:= j.1; let p:= fromBead G j; let a:= p.2.val.1; let b:=p.2.val.2
  refine (rigidHelm (fun x=> X x -Y x) j).trans ?_
  change ‖X p-Y p‖≤_
  let V:= spine U o
  obtain ⟨h₁,h₂,h₃,h₄⟩:= therm B o p hj
  have ht' : faceValue V p = V (z,a)*V (z+step a,b)*(V (z+step b,a))⁻¹*(V (z,b))⁻¹:= by
    unfold faceValue; simp only [square,travel,Step.vec_pos,Step.vec_neg,Step.pos_read,Step.neg_read,mul_one]
    simp only [← sub_eq_add_neg]; rw [show p.1+step p.2.val.1+step p.2.val.2-step p.2.val.1=p.1+step p.2.val.2 by abel,add_sub_cancel_right]; rw [← mul_assoc,←mul_assoc]; rfl
  let s:= 4*B*τ
  have h :∀ e : Edge (Site n), e∈Room o B→ somata o U c B e=c⁻¹ • G.curvature (V e):=fun i hp=> if_pos hp
  have hw: X p-Y p=c⁻¹ • (G.curvature (faceValue V p)-(G.curvature (V (z,a))+G.curvature (V (z+step a,b))- G.curvature (V (z+step b,a))-G.curvature (V (z,b)))):= by
    unfold X Y kiosk rho; dsimp only
    simp_rw [smul_sub,smul_add]; rw [h _ h₁,h _ h₂,h _ h₃, h _ h₄]; rfl
  rw [hw, ht',norm_smul, Real.norm_of_nonneg (inv_pos.mpr hc|>.le), ← div_eq_inv_mul]; exact div_le_div_of_nonneg_right (warp4 (wing o U hu hz ht _ h₁) (wing o U hu hz ht _ h₂) (wing o U hu hz ht _ h₄) (wing o U hu hz ht _ h₃)) hc.le
end YM.Next.Rank.Tapes
