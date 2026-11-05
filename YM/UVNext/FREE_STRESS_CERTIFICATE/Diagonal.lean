import YM.Next.UV_STRESS.Across
import YM.UVNext.FREE_STRESS_CERTIFICATE.Planes
import YM.UVNext.FREE_STRESS_CERTIFICATE.Samples


/-!
# No equation or separated null at weight four

No general reflected detector required: at unit axial separation the curl block
itself is invertible (indefinite without reflection). -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Wick Climb Labels Analysis Table Next.UVStress Function Set
open scoped RealInnerProductSpace
variable {G : Gauge} (F : Frames G)

def camera (i : Axis) : Points 2 := points (readings (YM.basis i) 0)
@[simp] theorem camera_ab (i) : camera i 0=YM.basis i := rfl
@[simp] theorem camera_zero (i) : camera i 1=0 := read_one (YM.basis i) 0
theorem shutter (i : Axis) : camera i ∈ conf 2 := by
  have hi : camera i 0 ≠ camera i 1 := fun h => one_ne_zero (α:=ℝ) (by simpa using congr_arg norm h)
  intro a b h; fin_cases a <;> fin_cases b
  exacts [rfl,(hi h).elim,(hi h.symm).elim,rfl]

def greenAxis (i t k : Axis) : ℝ :=
    if i=t ∧ k=t then 6*normal else if k=i then -(2*normal) else 0
private theorem radialAxis (i t k : Axis) : Maxwell.grad k (Maxwell.grad i Green) (YM.basis t) = greenAxis i t k := by
  rw [second_Green (by intro h; simpa using congr_arg norm h)]
  by_cases h : i=t <;> by_cases w : k=t <;> by_cases v : k=i <;>
    simp_all [basis_eq, greenAxis] <;> first | ring1 | (intro hx; subst k; contradiction)

-- time-independent choice of `t` here (any coordinate reflection).
def coat (t : Axis) (p : Plane) : ℝ := if p.val.1=t ∨ p.val.2=t then -(4*normal) else 4*normal

theorem coat_ne (t : Axis) (p : Plane) : coat t p ≠ 0 := by
  have h := Maxwell.normal_pos; unfold coat; split <;> linarith

theorem bare_diagonal (p q : Plane) (t : Axis) :
    bareCurl p.val.1 p.val.2 q.val.1 q.val.2 (YM.basis t) = if p=q then coat t p else 0 := by
  have ht : YM.basis t ≠ 0 := fun h => one_ne_zero (α:=ℝ) (by simpa using congr_arg norm h)
  simp only [bareCurl,Pi.sub_apply,Bare.opp_grad ht, radialAxis]
  by_cases he : p=q
  · subst q
    have H : p.val.1 ≠ p.val.2 := p.property.ne
    by_cases hv : p.val.1=t <;> by_cases hq : p.val.2=t
    all_goals first | exact (H (hv.trans hq.symm)).elim | (simp [coat,greenAxis,hv,hq,H,Ne.symm H]; first | ring1 | (split_ifs <;> first | ring1 | grind))
  rw [if_neg he]
  have h1 : p.val.1 < p.val.2 := p.property
  have h2 : q.val.1 < q.val.2 := q.property
  have hn : ¬ (p.val.1=q.val.1 ∧ p.val.2=q.val.2) := fun h => he (Subtype.ext (Prod.ext h.1 h.2))
  have h3 (a b : Axis) (h : a ≠ b) : greenAxis a t b = 0 := by
    unfold greenAxis; rw [if_neg (fun H => h (H.1.trans H.2.symm)), if_neg (Ne.symm h)]
  rw [show (if q.val.1 = p.val.2 then greenAxis q.val.2 t p.val.1 else 0) = 0 by
        split <;> rename_i hx
        · apply h3; rw [hx] at h2; exact (h1.trans h2).ne'
        rfl, show (if q.val.2=p.val.2 then greenAxis q.val.1 t p.val.1 else 0) = 0 by
        split <;> rename_i hx
        · exact h3 _ _ (fun h => hn ⟨h.symm,hx.symm⟩)
        rfl, show (if q.val.1=p.val.1 then greenAxis q.val.2 t p.val.2 else 0)=0 by
        split <;> rename_i hx
        · exact h3 _ _ (fun h => hn ⟨hx.symm,h.symm⟩)
        rfl, show (if q.val.2=p.val.1 then greenAxis q.val.1 t p.val.2 else 0)=0 by
        split <;> rename_i hx
        · apply h3; rw [hx] at h2; exact (h2.trans h1).ne
        rfl]
  simp

-- Normalized rank readers on the *same quotient* (not a norm estimate).
def negative (t : Axis) (p q : Plane) : (freeTable F).Field 4 →ₗ[ℂ] ℂ :=
    hearing F (camera t) p.val.1 p.val.2 q.val.1 q.val.2 4

theorem negative_unit (t p q) : negative F t p q (embed F 4 (Labels.unit G 4))=0 := by
  rw [pin_unit,negative,listens,Table.at_unit (freeTable F) (table_regular F) (shutter t)]
  let S := freeTable F
  let P := two G 4 le_rfl p q
  let x := Points.tail (camera t)
  change S.useAt S x (fun _ => tag F 4 P) = 0
  have hx : x ∈ conf _ := Points.tail_in (n:=1) (shutter t)
  let w : Fin 0 → (standard F).Token := Fin.elim0
  rw [show (fun _ : Fin 1 => tag F 4 P) = S.classTokens ∘ Fin.cons (α:=fun _ => (standard F).Token) (token F 4 P) w from
      funext fun i => by rw [Subsingleton.elim i 0]; rfl, S.at_project S (table_sym F) (fun _ => le_rfl) hx,first_label]
  unfold P two ff; rw [shell_bond]
  let f : WickPol G →ₗ[ℂ] ℂ := (moment G x).toLinearMap (fun _ => 0) 0
  have hh (v : WickPol G) (z : Fin 0 → WickPol G) : moment G x (Fin.cons v z) = f v := by
    apply congr_arg (fun u : Fin 1 → WickPol G => moment G x u); funext i; rw [@Subsingleton.elim (Fin 1) _ i 0]; simp
  rw [hh,map_sum]
  apply Finset.sum_eq_zero; intro i _
  have ht := mean_symbol x (curlProbe (initialPlace p.val.1 p.val.2) i) (curlProbe (initialPlace q.val.1 q.val.2) i)
  rw [← hh _ (z:=fun _ => 0)]
  convert ht using 2
  funext k; rw [@Subsingleton.elim (Fin 1) _ k 0]; rfl

private lemma dim_positive (h : G.Simple) : 0 < G.lieDim := by
  rw [Gauge.lieDim, ← G.colorIso.finrank_eq]
  haveI := h.nontrivial_color
  exact Module.finrank_pos

def reader (t : Axis) (p q : Plane) : (freeTable F).Field 4 →ₗ[ℂ] ℂ :=
  ((G.lieDim:ℂ) * (coat t p : ℂ) * (coat t q : ℂ))⁻¹ • negative F t p q

lemma reader_two (h : G.Simple) (p q c r : Plane) (t : Axis) :
    reader F t p q (embed F 4 (two G 4 le_rfl c r)) =
    ((if c=p then (1:ℂ) else 0) * (if r=q then 1 else 0) + (if c=q then 1 else 0) * (if r=p then 1 else 0)) := by
  have hn : (G.lieDim:ℂ) ≠ 0 := by exact_mod_cast (dim_positive h).ne'
  have he (i : Plane) : (coat t i:ℂ) ≠ 0 := by exact_mod_cast coat_ne t i
  unfold reader two negative
  rw [LinearMap.smul_apply,smul_eq_mul,hears F (shutter t),camera_zero,camera_ab,sub_zero,flash,
    bare_diagonal c p t,bare_diagonal r q t,bare_diagonal c q t,bare_diagonal r p t]
  have ht (i k : Plane) : (if i=k then coat t i else 0) = (coat t k) * (if i=k then 1 else 0) := by split_ifs <;> simp_all
  simp_rw [ht]
  push_cast
  have w (i k : Plane) : ((↑(if i=k then 1 else (0:ℝ)):ℂ)) = if i=k then 1 else 0 := by split_ifs <;> simp
  simp_rw [w]
  have hp := he p; have hq := he q
  field_simp











end YM.UVNext.FreeStress
