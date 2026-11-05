import YM.Next.RANK.Zephyr
/-!
# Ad transports for leading W error from affine link atlas

Orbit rotation from ONE frame, no replacing tag predictions after W weights.
Do not require affine mean in our specific Spindle axial gauge. Support measured
in full Rank epoch. This estimates at finite normalized coordinates from more
primitive link-side estimate receipts of the ONE-step kernels. Still an explicit
construction prerequisite.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function Filter MeasureTheory Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Beamer
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G : Gauge} {Ω T V : Type*}



abbrev linkColor (G : Gauge) (p : Side) := Edge (Site p) × G.ColorIndex
abbrev linksOn (G : Gauge) (n : Side) := Edge (Site n) → G.Color
variable {n : Side}
def valves (u : linkColor G n → ℝ) : linksOn G n := fun i=> WithLp.toLp _ fun j=> u (i,j)

def stem (f : bead G n) : linkColor G n →₀ ℂ :=
   let x:= f.1; let (a,b):= f.2.1.val;let c:=f.2.2
   (Finsupp.single ((x,a),c) 1 + Finsupp.single ((x+step a,b),c) 1)-Finsupp.single ((x+step b,a),c) 1- Finsupp.single ((x,b),c) 1

def froth (u : linksOn G n) : bead G n→ℝ:=rigid (rho u)
@[simp] lemma sparks (F : bead G n) (A B : linksOn G n) : froth (A+B) F=froth A F+froth B F:= by
  unfold froth rigid rho; dsimp only; simp only [Pi.add_apply,PiLp.add_apply,PiLp.sub_apply]; abel


-- ungauged correction uses weave once. any link path within stencil.
lemma impulse {j : Walk} (p : Cover) {U : CoverConfig G} {r : ℝ} (_ : 0 ≤ r) (h : ∀ e : Edge Cover,e.1 ∈ visits p j → e.1+step e.2 ∈ visits p j → G.chord (U e) ≤ r): G.chord (travel U p j) ≤ j.length*r:= by
  induction j generalizing p with
  | nil=> simp [travel]
  | cons y z IH=>
    have he x (h : x∈visits (p+y.vec) z):x∈visits p (y::z):=List.mem_cons_of_mem _ h
    have hh := IH (p+y.vec) (fun i a b=> h _ (he _ a) (he _ b))
    have ht : G.chord (y.read U p)≤r:= by
      have hx:p∈visits p (y::z):=List.mem_cons_self
      have hy:p+y.vec∈visits p (y::z):= he _ (by cases z <;>simp [visits])
      rcases y with ⟨a,_|_⟩
      · exact h (p,a) hx hy
      change G.chord ((negDir a).read U p)≤r
      rw [Step.neg_read,G.chord_inv]; exact h _ (by simpa only [Step.vec, Step.neg_read,↓reduceIte, ←sub_eq_add_neg] using hy) (by simpa only [sub_add_cancel] using hx)
    rw [travel]; apply le_trans (G.chord_triangle _ _) ((add_le_add ht hh).trans ?_); simp; linarith only
variable {g t R δ : ℝ} {o : Site n} {B : ℕ}
lemma linked (u : Config G n) (_ : 2*(B+1)< n.val) (ht : 0≤t)
    (F : ∀ i, i∈Room o B → G.chord (u i) ≤ t) (y : Site n) (H : y∈ Spindle.patch B o) : G.chord (fingers u o y)≤ 4*B*t:= by
  let b:=lift (y-o); have hr : b∈box B:=Work.E08.lift_mem_box ((doors y|>.1) H)
  let j:= paths b; have hb : j.length≤4*B := (Spindle.lengths b).trans_le (Spindle.bounded hr)
  apply (impulse (j:=j) 0 ht (show ∀ e : Edge Cover, e.1∈visits 0 j→e.1+step e.2∈visits 0 j → G.chord (expandAt o u e) ≤ t from ?_)).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hb) ht)
  rintro ⟨z,i⟩ hx hz
  exact F (edgeAt z o i) (Spindle.reads ⟨(z,i),⟨village b hr _ hx,village b hr _ hz⟩⟩ o).property

lemma gyro (u v : G.El) {t₁ t₂ : ℝ} (hu : G.chord u ≤ t₁) (hv : G.chord v ≤ t₂) :
    ‖G.curvature (u*v*u⁻¹) - G.curvature v‖ ≤ G.colorScale*(t₁*t₂ +(t₁+t₂)*t₁):= by
  let κ:=G.curvature; let s:=G.colorScale; have hf:=G.colorScale_pos
  have hx (v w : G.El) (x y : ℝ) (h : G.chord v≤x) (ht : G.chord w≤y): ‖κ (v*w)-(κ v+κ w)‖≤ s*x*y := by
    exact (weave ..).trans (mul_le_mul (mul_le_mul_of_nonneg_left h hf.le) ht (G.chord_nonneg _) (mul_nonneg hf.le ((G.chord_nonneg v).trans h)))
  have hp := hx u v t₁ t₂ hu hv
  have hk:=hx (u*v) u⁻¹ _ _ ((G.chord_triangle u v).trans (add_le_add hu hv)) ((G.chord_inv u).trans_le hu)
  apply (norm_sub_le_norm_sub_add_norm_sub _ (κ (u*v)+κ u⁻¹) _).trans (le_trans (b:=s*(t₁+t₂)*t₁+s*t₁*t₂) (add_le_add hk ?_) (le_of_eq (by unfold s; ring)))
  rw [show (κ (u*v)+κ u⁻¹)-(G.curvature v)= κ (u*v) -(κ u+κ v) by unfold κ;rw [G.curvature_inv];abel];exact hp

private lemma face_auth (U : Config G n) (p : Face (Per n)) : faceValue U p=
    let z:= p.1; let a:=p.2.val.1; let b:=p.2.val.2
    U (z,a)* U (z+step a,b)*(U (z+step b,a))⁻¹*(U (z,b))⁻¹:= by
  unfold faceValue; simp only [square,travel,Step.vec_pos,Step.vec_neg,Step.pos_read,Step.neg_read,mul_one]; simp only [← sub_eq_add_neg]; rw [show p.1+step p.2.val.1+step p.2.val.2-step p.2.val.1=p.1+step p.2.val.2 by abel,add_sub_cancel_right]; rw [← mul_assoc,←mul_assoc]

lemma four_corners (Y : bead G n) (hp : separation o Y.1 + 2 ≤ B) (X W : linksOn G n) (hx : ∀ e,e∈Room o B → ‖X e-W e‖≤δ): |froth X Y-froth W Y| ≤ 4*δ:= by
  let p:= fromBead G Y; let v:=p.1;let i:= p.2.val.1; let j:=p.2.val.2
  let S:= X-W; let y:=rho X-rho W
  apply (rigidHelm y Y).trans
  change ‖y p‖ ≤ _
  obtain ⟨h₁,h₂,h₃,h₄⟩:=therm B o p hp
  have he a (ha) : ‖S a‖ ≤δ:=hx a ha
  rw [show y p=rho S p by unfold y S rho; simp only [Pi.sub_apply]; abel]
  apply (norm_sub_le ..).trans (le_trans (add_le_add (le_trans (norm_sub_le ..) (add_le_add (le_trans (norm_add_le ..) (add_le_add (he _ h₁) (he _ h₂))) (he _ h₄))) (he _ h₃)) (by linarith only))

def nautical (G : Gauge) (t g : ℝ) (B : ℕ):= let T:=4*B*t
                            (G.colorScale*(T*(4*t)+(T+4*t)*T)+6*G.colorScale*t^2)/g

-- estimate in arbitrary near-identity frame. Apply per pose; T.heat bounds supplied together.
lemma crested (u : Config G n) (h : 2*(B+1)< n.val) (hg : 0<g) (ht : 0≤t)
    (f : Site n →G.El) (k : bead G n) (hk : separation o k.1+2 ≤ B)
    (F : ∀ i,i∈Room o B → G.chord (Lattice.gauge f u i) ≤ t) :
    let Z (i : Edge _) := g⁻¹ • G.curvature (Lattice.gauge f u i)
    |rigid (coloring (f o) (kiosk g o u)) k - froth Z k| ≤ nautical G t g B:= by
  intro Z; let V:=Lattice.gauge f u; let j:=fromBead G k; let x:=j.1; let a:=j.2.val.1;let b:=j.2.val.2;let p:=faceValue V j
  have hp : separation o x+2≤B:= hk
  rw [show rigid (coloring (f o) (kiosk g o u)) k=rigid (kiosk g o V) k from congr_arg (fun z:G.Color=> z k.2.2) (keyGauges g o u j f hp h).symm]
  apply (rigidHelm ((kiosk g o V)-rho Z) k).trans
  obtain ⟨h₁,h₂,h₃,h₄⟩:=therm B o j hp
  have hu:= warp4 (F _ h₁) (F _ h₂) (F _ h₄) (F _ h₃)
  let κ := G.curvature;let C:=G.chord
  have hV:C p ≤ 4*t := by
    unfold p; rw [face_auth];
    apply (G.chord_triangle _ _).trans (le_trans (add_le_add (le_trans (G.chord_triangle _ _) (add_le_add (le_trans (G.chord_triangle _ _) (add_le_add (F _ h₁) (F _ h₂))) ((G.chord_inv _).trans_le (F _ h₄)))) ((G.chord_inv _).trans_le (F _ h₃))) (by linarith only))
  let c:= fingers V o x
  have he:c*p*c⁻¹=faceValue (spine V o) j:= by unfold spine; rw [face_gauge]
  let z:= κ (V (x,a))+κ (V (x+step a,b))-κ (V (x+step b,a))-κ (V (x,b)); let u:= 4*B*t
  change ‖(kiosk g o V-rho Z) j‖ ≤ _
  rw [show (kiosk g o V-rho Z) j=g⁻¹ • (κ (c*p*c⁻¹)-z) by rw [he]; unfold κ z Z rho kiosk; dsimp only [Pi.sub_apply]; simp only [smul_add,smul_sub]; rfl]; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hg|>.le),← div_eq_inv_mul]
  apply div_le_div_of_nonneg_right ?_ hg.le
  apply (norm_sub_le_norm_sub_add_norm_sub _ (κ p) _).trans
  have hZ:= gyro c p (linked V h ht F x ((doors x).2 (by omega))) hV
  refine add_le_add hZ ?_
  unfold p;rw [face_auth]; exact hu
end YM.Next.Rank.Tapes
