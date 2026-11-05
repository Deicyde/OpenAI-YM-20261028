import YM.Pert.Lattice.Lifts
/-! Multilinear tested data at one finite regulator through one physical horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Full
open Lattice Bare Orb Maxwell RawLabels Function Filter MvPolynomial Labels MeasureTheory
open scoped Topology Matrix.Norms.Frobenius
variable {G : Gauge} {d e : ℕ} {N : Side}
abbrev Phi (G : Gauge) (N : Side) := JetArray (Coords G N)
lemma column_linear_add (h : ℝ) (o : Site N) (p q : Pol G) : column d h o (p+q)=column d h o p+column d h o q := paint_sum ..
lemma column_linear_smul (r : ℂ) (h : ℝ) (o : Site N) (p : Pol G) : column d h o (r • p)= r • column d h o p := by
  ext1 v
  simp only [auxiliary, MvPolynomial.smul_eq_C_mul,pairEval,map_mul, eval₂Hom_C, Pi.smul_apply, PowerSeries.smul_eq_C_mul]
  exact avg_const_mul (PowerSeries.C r) (fun w=> pairEval h o v w p) h (leg_ready h o v p)
def columnMap (d : ℕ) (h : ℝ) (o : Site N) : Pol G →ₗ[ℂ] Phi G N where
  toFun := column d h o
  map_add' x y := column_linear_add ..
  map_smul' x y := column_linear_smul ..

def space (G : Gauge) (N : Side) : Submodule ℂ (Phi G N) where
  carrier := setOf Ready
  zero_mem' := Ready.constant _
  add_mem' h j := Ready.add h j
  smul_mem' c f j := by
    rw [show c • _ = (fun _ : Coords G N => PowerSeries.C c) * _ from funext fun v => PowerSeries.smul_eq_C_mul ..]; exact Ready.mul (Ready.constant _) j

def vacuumMap (G : Gauge) (N : Side) : ↥(space G N) →ₗ[ℂ] PowerSeries ℂ where
  toFun p := normalize p.val
  map_add' p q := normalize_add p.property q.property
  map_smul' r p := by change normalize (r • p.val) = r • _; rw [show r • p.val = _ from funext fun _ => PowerSeries.smul_eq_C_mul ..,PowerSeries.smul_eq_C_mul]; exact normalize_shift _ p.property

variable (d)
variable {r : ℕ} {Frame : Frames G}
abbrev Source := (freeTable Frame).Field d
def sections (Frame : Frames G) : Source (Frame:=Frame) d →ₗ[ℂ] Pol G := (Labels.localFields G d).subtype ∘ₗ physicalLabel Frame d

def polynomialRow (Frame : Frames G) (h : ℝ) (o : Fin r → Site N) : MultilinearMap ℂ (fun _ : Fin r => Source (Frame:=Frame) d) (Phi G N) :=
  (MultilinearMap.mkPiAlgebra ℂ (Fin r) (Phi G N)).compLinearMap (fun i => columnMap d h (o i) ∘ₗ sections d Frame)
lemma row_eq (h : ℝ) (o : Fin r → Site N) (p : Fin r → Source (Frame:=Frame) d) : polynomialRow d Frame h o p = product (fun _ => d) h Finset.univ o (sections d Frame ∘ p) := rfl

def row (Frame : Frames G) (h : ℝ) (o : Fin r → Site N) : MultilinearMap ℂ (fun _ : Fin r => Source (Frame:=Frame) d) (PowerSeries ℂ) :=
    (vacuumMap G N).compMultilinearMap (polynomialRow d Frame h o |>.codRestrict (space G N) (fun p => show _ from (show Ready _ from (row_eq d h o p).symm ▸ product_ready (fun _ => d) h Finset.univ o (sections d Frame ∘ p))))
lemma row_def (h : ℝ) (o : Fin r → Site N) (p : Fin r → Source (Frame:=Frame) d) : row d Frame h o p = amplitude (fun _ => d) h Finset.univ o (sections d Frame ∘ p) := rfl
abbrev Grid (D : Side) (r : ℕ) := Fin r → Site D
/-- Side schedule: top spacing `L^(-m)` in reporting units, side `4*(L.val)^(m^2+m+1)` in top units, report after taking the order. -/
def topSpacing (L : Side) (m : ℕ) : ℝ := (L.val:ℝ)^(-(m:ℤ))
lemma spacing_pos (L : Side) (m : ℕ) : 0 < topSpacing L m := by unfold topSpacing; positivity

def period (L : Side) (m : ℕ) : Side := ⟨4*L.val^(m^2+m+1), by positivity⟩
lemma sized (L : Side) (m) : Admissible (period L m) := by unfold Admissible period; dsimp; exact ⟨Nat.le_mul_of_pos_right _ (by positivity), dvd_mul_of_dvd_left (by decide) _⟩
/-- Report around an origin at the quarter side in each component. One can also keep native offset roots in the inputs to row. -/
def center (N : Side) : Site N := fun _ : Axis=> ((N.val/4:ℕ):ZMod N.val)
def embedding (h : ℝ) (x : Grid N r) : Points r := points (fun i => WithLp.toLp 2 (fun k : Axis => h * ((Lattice.lift (x i-center N) k):ℝ)))

def profile (r : ℕ) (Frame : Frames G) (L : Side) (m : ℕ) (f : Points r→ℂ) : MultilinearMap ℂ (fun _ : Fin r=> Source (Frame:=Frame) d) (PowerSeries ℂ) :=
    ∑ o : Grid (period L m) r, ((topSpacing L m:ℂ)^(4*r) * f (embedding (topSpacing L m) o)) • row d Frame (topSpacing L m) o
lemma row_includes (hd : d≤e) (W : DiffPlan (freeTable Frame)) (HW : W.Inclusions (freeTable Frame)) (h : ℝ) (o : Grid N r) (p : Fin r→Source (Frame:=Frame) d) :
    row d Frame h o p=row e Frame h o (W.rise hd ∘ p) := by
  simp only [row_def]
  rw [show sections e Frame ∘ W.rise hd ∘ p=sections d Frame ∘ p from funext (fun i => congrArg (fun q : Label G e => q.val) (physical_inclusion Frame HW hd (p i)))]
  exact amplitude_agrees _ _ (fun _ _ => hd) (fun i _ => height_le (physicalLabel Frame d (p i))) _ _
lemma profile_coherent (hd : d≤e) (W : DiffPlan (freeTable Frame)) (HW : W.Inclusions (freeTable Frame)) (L m) (f : Points r→ℂ) (p : Fin r→Source (Frame:=Frame) d) : profile d r Frame L m f p = profile e r Frame L m f (W.rise hd ∘ p) := by
  simp_rw [profile,MultilinearMap.sum_apply,MultilinearMap.smul_apply,row_includes d hd W HW]
end YM.Pert.Full
