import YM.Work.A01.Support

/-!
# Real and H transformations of local fluxes

Real and mirroring are *separate* operations; no OS reflecting-star
in this argument. We use all signed permutations, including improper.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.A01
open Table Analysis Function Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {L : Register G} {S : Table L} {d n : ℕ}

def realTag (H : S.RealSpin) (q : S.Tag) : S.Tag := ⟨q.1,S.conj H q.1 q.2⟩
def mirrorTag (H : S.RealSpin) (k : Signed) (q : S.Tag) : S.Tag := ⟨q.1,S.mirror H q.1 k q.2⟩

theorem real_eval (h : S.Symmetric) (H : S.RealSpin) {x : Points n} (hx : x ∈ conf _)
    (q : Fin n → S.Tag) : S.useAt S x (realTag H ∘ q) = star (S.useAt S x q) := by
  let t := Ward.expose ∘ q
  have he (p : L.Token) : S.classTokens (L.conjugate p) = realTag H (S.classTokens p) := rfl
  have ht : realTag H ∘ q = S.classTokens ∘ (L.conjugate ∘ t) := by
    funext i; simp only [t, Function.comp_apply, he, Ward.sends_back]
  rw [ht, S.at_project S h (fun _ => le_rfl) hx, H.real hx]
  rfl

theorem mirror_eval (h : S.Symmetric) (H : S.RealSpin) {x : Points n} (hx : x ∈ conf _)
    (q : Fin n → S.Tag) (k : Signed) :
    S.useAt S (Points.move k.ortho x) (mirrorTag H k ∘ q) = S.useAt S x q := by
  let t := Ward.expose ∘ q
  have he (p : L.Token) : S.classTokens (L.move k p) = mirrorTag H k (S.classTokens p) := rfl
  have ht : mirrorTag H k ∘ q = S.classTokens ∘ (L.move k ∘ t) := by
    funext i; simp only [t, Function.comp_apply, he, Ward.sends_back]
  rw [ht, S.at_project S h (fun _ => le_rfl) (Points.move_in _ hx), H.mirror k hx]
  rfl

/-- The all-spectator quotient is tested over the same set of words after bar. -/
theorem ext_against_real (h : S.Symmetric) (H : S.RealSpin) {A B : S.Field d}
    (p : ∀ n (q : Fin n → S.Tag), ∀ x ∈ conf (n+1),
      S.useAt S x (Fin.cons ⟨d,A⟩ (realTag H ∘ q)) = S.useAt S x (Fin.cons ⟨d,B⟩ (realTag H ∘ q))) :
    A = B := by
  apply S.field_ext h
  intro n q x hx
  have he := p n (realTag H ∘ q) x hx
  rwa [show realTag H ∘ realTag H ∘ q = q from funext fun i => by
    change ⟨(q i).1,S.conj H _ (S.conj H _ (q i).2)⟩=q i
    rw [S.reflect_star H]] at he

/-- Likewise we lose no spectators by testing on rotated points and labels. -/
theorem ext_against_mirror (h : S.Symmetric) (H : S.RealSpin) (k : Signed) {A B : S.Field d}
    (p : ∀ n (q : Fin n → S.Tag), ∀ x ∈ conf (n+1),
      S.useAt S (Points.move k.ortho x) (Fin.cons ⟨d,A⟩ (mirrorTag H k ∘ q)) =
        S.useAt S (Points.move k.ortho x) (Fin.cons ⟨d,B⟩ (mirrorTag H k ∘ q))) :
    A = B := by
  apply S.field_ext h
  intro n q x hx
  have he := p n (mirrorTag H k⁻¹ ∘ q) (Points.move k.ortho⁻¹ x) (Points.move_in _ hx)
  have hm : mirrorTag H k ∘ mirrorTag H k⁻¹ ∘ q = q := by
    funext i; change ⟨(q i).1,S.mirror H _ k (S.mirror H _ k⁻¹ (q i).2)⟩ = q i
    rw [← S.mirror_mul, mul_inv_cancel, S.mirror_one]
  rwa [show Points.move k.ortho (Points.move k.ortho⁻¹ x)=x from by ext1 i; simp, hm] at he

theorem flux_real (h : S.Symmetric) (H : S.RealSpin) (J : S.Stress)
    (hr : ∀ a b, S.conj H 4 (J a b) = J a b) {x : Points (n+1)} (hx : x ∈ conf _)
    {χ : E4 → ℝ} (hw : Window x χ) (V : E4 → E4) (q : Fin n → S.Tag) (B : S.Field d) :
    flux J χ V x (realTag H ∘ q) (S.conj H d B) = star (flux J χ V x q B) := by
  have ht (a b : Axis) (y : E4) : term J χ V x (realTag H ∘ q) (S.conj H d B) a b y =
      star (term J χ V x q B a b y) := by
    by_cases hz : D (basis a) χ y = 0
    · simp [term, hz]
    have he := real_eval h H (separated_of_D hx hw hz) (Fin.cons ⟨4,J a b⟩ (Fin.cons ⟨d,B⟩ q))
    rw [comp_cons, comp_cons, show realTag H (⟨4,J a b⟩:S.Tag) = ⟨4,J a b⟩ from by simp [realTag,hr],
      show realTag H (⟨d,B⟩:S.Tag)=⟨d,S.conj H d B⟩ from rfl] at he
    unfold term
    rw [he,star_mul'] -- comm case
    simp
  simp_rw [flux, ht, star_neg, star_sum, Complex.star_def, integral_conj]

/-! H acts by permutation of the coordinates with signs on the input axes. -/

def eps (k : Signed) (i : Axis) : ℝ := k.matrix (k.perm i) i

theorem eps_self (k : Signed) (i : Axis) : eps k i * eps k i = 1 := by
  unfold eps
  rw [Signed.matrix_at]; split_ifs <;> simp_all

theorem eps_column (k : Signed) (i : Axis) (f : Axis → S.Field d) :
    ∑ j : Axis, ((k.matrix j i : ℝ) : ℂ) • f j = (eps k i : ℂ) • f (k.perm i) := by
  rw [Finset.sum_eq_single_of_mem (k.perm i) (Finset.mem_univ _)]
  · rfl
  · intro b _ hb; simp [Signed.matrix_at,Ne.symm hb]

theorem tensor_column {H : S.RealSpin} {J : S.Stress} (h : RawTensor H J) (k : Signed)
    (a b : Axis) : S.mirror H 4 k (J a b) =
      ((eps k a * eps k b : ℝ) : ℂ) • J (k.perm a) (k.perm b) := by
  rw [h]; simp_rw [Complex.ofReal_mul, mul_smul, ← Finset.smul_sum]
  simp_rw [eps_column]

theorem move_coordinate (k : Signed) (y : E4) (a : Axis) :
    Ortho.move k.ortho y (k.perm a) = eps k a * y a := by
  rw [Signed.ortho_move]
  change k.act _ _ = _
  cases e : k.flip a <;> simp [eps, Signed.matrix_at,e]

theorem move_basis (k : Signed) (a : Axis) : Ortho.move k.ortho (basis a) = eps k a • basis (k.perm a) := by
  ext1 j
  obtain ⟨i,rfl⟩ := k.perm.surjective j
  by_cases he : i=a
  · subst i; simp [move_coordinate]
  · simp [move_coordinate,he]

/-- Push the same window along the position isometry. -/
def shifted (K : Ortho) (χ : E4 → ℝ) : E4 → ℝ := χ ∘ (Ortho.motion K).symm

theorem window_move (K : Ortho) {x : Points (n+1)} {χ : E4 → ℝ} (w : Window x χ) :
    Window (Points.move K x) (shifted K χ) := by
  let e := Ortho.motion K
  refine ⟨w.1.comp e.symm.contDiff, w.2.1.comp_homeomorph e.symm.toHomeomorph, ?_, ?_⟩
  · change χ ∘ ⇑e.symm =ᶠ[𝓝 (e (x 0))] (fun _ => 1)
    have hm : Tendsto e.symm (𝓝 (e (x 0))) (𝓝 (x 0)) := by
      simpa using (e.symm.continuous.tendsto (e (x 0)))
    exact w.2.2.1.comp_tendsto hm
  · intro i
    change e (x i.succ) ∉ tsupport (χ ∘ e.symm.toHomeomorph)
    rw [tsupport_comp_eq_preimage]
    change e.symm (e (x i.succ)) ∉ tsupport χ
    rw [e.symm_apply_apply]; exact w.2.2.2 i

theorem shifted_D (k : Signed) {χ : E4 → ℝ} (hw : ContDiff ℝ ∞ χ) (y : E4) (a : Axis) :
    D (basis (k.perm a)) (shifted k.ortho χ) (Ortho.move k.ortho y) = eps k a * D (basis a) χ y := by
  let E := Ortho.motion k.ortho
  let e := E.toContinuousLinearEquiv.toContinuousLinearMap
  let f := shifted k.ortho χ
  have hF : f ∘ e = χ := funext fun x => by change χ (E.symm (E x))=_; rw [E.symm_apply_apply]
  have he : ContDiff ℝ ∞ f := hw.comp E.symm.contDiff
  have hx : D (basis a) χ y = eps k a * D (basis (k.perm a)) f (e y) := by
    conv_lhs => rw [← hF]
    change fderiv ℝ (f ∘ e) y _ = _
    rw [fderiv_comp y (he.differentiable (by simp) _) e.differentiableAt, e.fderiv,
      ContinuousLinearMap.comp_apply, show e (basis a) = _ from move_basis k a, map_smul]; rfl
  rw [hx, ← mul_assoc, eps_self, one_mul]; rfl

theorem move_cons (K : Ortho) (x : Points n) (y : E4) :
    Points.move K (Points.cons y x) = Points.cons (Ortho.move K y) (Points.move K x) := by
  ext1 i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [Points.cons]

/-- Angular vector field about the pushed center. In particular this is the adjoint H action. -/
theorem move_rotation (k : Signed) (u : Ortho.Skew) (x y : E4) :
    M4.move (Org.orients k u).val (Ortho.move k.ortho y - Ortho.move k.ortho x) =
      Ortho.move k.ortho (M4.move u.val (y-x)) := by
  rw [show Ortho.move k.ortho y - Ortho.move k.ortho x = Ortho.move k.ortho (y-x) from
    (map_sub (Ortho.motion _) y x).symm]
  let K := k.ortho
  change M4.move (K.val*u.val*star K.val) (M4.move K.val (y-x)) = M4.move K.val _
  rw [← M4.move_mul, mul_assoc (K.val*u.val), show star K.val*K.val=1 from K.property.1,
    mul_one, M4.move_mul]

theorem flux_mirror (h : S.Symmetric) (H : S.RealSpin) (J : S.Stress) (ht : RawTensor H J)
    (k : Signed) {x : Points (n+1)} (hx : x ∈ conf _) {χ : E4 → ℝ} (hw : Window x χ)
    (V Q : E4 → E4) (hv : ∀ y, Q (Ortho.move k.ortho y) = Ortho.move k.ortho (V y))
    (q : Fin n → S.Tag) (B : S.Field d) :
    flux J (shifted k.ortho χ) Q (Points.move k.ortho x) (mirrorTag H k ∘ q) (S.mirror H d k B) =
      flux J χ V x q B := by
  let r := Fin.cons (α := fun _ : Fin (n+1) => S.Tag) ⟨d,S.mirror H d k B⟩ (mirrorTag H k ∘ q)
  let E := Ortho.motion k.ortho
  let f := term J (shifted k.ortho χ) Q (Points.move k.ortho x) (mirrorTag H k ∘ q) (S.mirror H d k B)
  have hm (a b : Axis) (y : E4) : f (k.perm a) (k.perm b) (E y) = term J χ V x q B a b y := by
    unfold f term
    rw [show E y = Ortho.move k.ortho y from rfl, shifted_D k hw.1, hv y, move_coordinate]
    by_cases hz : D (basis a) χ y = 0
    · simp [hz]
    have he := mirror_eval h H (separated_of_D hx hw hz) (Fin.cons ⟨4,J a b⟩ (Fin.cons ⟨d,B⟩ q)) k
    rw [move_cons, comp_cons, comp_cons, show mirrorTag H k (⟨4,J a b⟩:S.Tag)=⟨4,S.mirror H 4 k (J a b)⟩ from rfl,
      tensor_column ht k] at he
    rw [← he]
    -- two signs on the stress alone; the gradient and V carry one each
    rw [← front_eval _ _ 4 (((eps k a * eps k b : ℝ) : ℂ) • J (k.perm a) (k.perm b)),
      map_smul, smul_eq_mul, front_eval]
    change _ = ((D (basis a) χ y * V y b : ℝ):ℂ) *
      (((eps k a * eps k b : ℝ):ℂ) * S.useAt S (Points.cons (Ortho.move k.ortho y) (Points.move k.ortho x))
        (Fin.cons ⟨4,J (k.perm a) (k.perm b)⟩ r))
    unfold r; push_cast; ring
  have hi (a b : Axis) : (∫ y, f (k.perm a) (k.perm b) y) = ∫ y, term J χ V x q B a b y := by
    rw [← E.measurePreserving.integral_comp E.toHomeomorph.measurableEmbedding]
    simp_rw [hm]
  unfold flux
  apply congr_arg Neg.neg
  change ∑ a, ∑ b, (∫ y, f a b y) = _
  rw [← Equiv.sum_comp k.perm (fun a => ∑ b, (∫ y, f a b y))]
  apply Finset.sum_congr rfl; intro a _
  rw [← Equiv.sum_comp k.perm (fun b => (∫ y, f (k.perm a) b y))]; simp_rw [hi]
end YM.Work.A01
