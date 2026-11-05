import YM.Bid.Drops

/-! Compatibility of the kernel differential system with the supplied real and signed
symmetries. Work on `conf` (a neighborhood of each point in question). -/
set_option autoImplicit false
noncomputable section
namespace YM.Work.D06
open Set Filter Function Analysis Points
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {L : Register G} {S : Table L} {n : ℕ}

def realTag (H : S.RealSpin) (q : S.Tag) : S.Tag := ⟨q.1, S.conj H q.1 q.2⟩
def signedTag (H : S.RealSpin) (s : Signed) (q : S.Tag) : S.Tag := ⟨q.1, S.mirror H q.1 s q.2⟩

theorem use_real (h : S.Symmetric) (H : S.RealSpin) {x : Points n} (hx : x ∈ conf n)
    (q : Fin n → S.Tag) : S.useAt S x (realTag H ∘ q) = star (S.useAt S x q) := by
  let v := Ward.expose ∘ q
  have e : S.classTokens ∘ (L.conjugate ∘ v) = realTag H ∘ q := by
    funext i
    change (⟨(q i).1, S.project _ (star (S.representative _ (q i).2))⟩ : S.Tag) = _
    rw [← S.conj_project H, S.rep]; rfl
  rw [← e, S.at_project S h (fun _ => le_rfl) hx, H.real hx]
  rfl

theorem use_signed (h : S.Symmetric) (H : S.RealSpin) (s : Signed) {x : Points n} (hx : x ∈ conf n)
    (q : Fin n → S.Tag) : S.useAt S (move s.ortho x) (signedTag H s ∘ q) = S.useAt S x q := by
  let v := Ward.expose ∘ q
  have e : S.classTokens ∘ (L.move s ∘ v) = signedTag H s ∘ q := by
    funext i
    change (⟨(q i).1, S.project _ (L.mirrorGroup _ s (S.representative _ (q i).2))⟩ : S.Tag) = _
    rw [← S.mirror_project H, S.rep]; rfl
  rw [← e, S.at_project S h (fun _ => le_rfl) (move_in _ hx), H.mirror s hx]
  rfl

theorem real_front (h : S.Symmetric) (H : S.RealSpin) {d : ℕ} (B : S.Field d)
    {x : Points (n+1)} (hx : x ∈ conf _) (q : Fin n → S.Tag) :
    S.useAt S x (Fin.cons ⟨d, S.conj H d B⟩ (realTag H ∘ q)) = star (S.useAt S x (Fin.cons ⟨d,B⟩ q)) := by
  simpa only [Fin.comp_cons, realTag] using use_real h H hx (Fin.cons ⟨d,B⟩ q)

theorem signed_front (h : S.Symmetric) (H : S.RealSpin) {d : ℕ} (B : S.Field d) (s : Signed)
    {x : Points (n+1)} (hx : x ∈ conf _) (q : Fin n → S.Tag) :
    S.useAt S (move s.ortho x) (Fin.cons ⟨d, S.mirror H d s B⟩ (signedTag H s ∘ q)) =
      S.useAt S x (Fin.cons ⟨d,B⟩ q) := by
  simpa only [Fin.comp_cons, signedTag] using use_signed h H s hx (Fin.cons ⟨d,B⟩ q)

theorem real_ext (h : S.Symmetric) (H : S.RealSpin) {d : ℕ} {A B : S.Field d}
    (eqs : ∀ (n : ℕ) (q : Fin n → S.Tag), ∀ x ∈ conf (n+1),
      S.useAt S x (Fin.cons ⟨d,B⟩ (realTag H ∘ q)) = star (S.useAt S x (Fin.cons ⟨d,A⟩ q))) :
    S.conj H d A = B := by
  apply S.field_ext h; intro n q x hx
  let q' := realTag H ∘ q
  have e : realTag H ∘ q' = q := by
    funext i; dsimp [realTag, q']; rw [S.reflect_star]
  exact (e ▸ ((real_front h H A hx q').trans (eqs n q' x hx).symm))

theorem signed_ext (h : S.Symmetric) (H : S.RealSpin) (s : Signed) {d : ℕ} {A B : S.Field d}
    (eqs : ∀ (n : ℕ) (q : Fin n → S.Tag), ∀ x ∈ conf (n+1),
      S.useAt S (move s.ortho x) (Fin.cons ⟨d,B⟩ (signedTag H s ∘ q)) = S.useAt S x (Fin.cons ⟨d,A⟩ q)) :
    S.mirror H d s A = B := by
  apply S.field_ext h; intro n q x hx
  let q' := signedTag H s⁻¹ ∘ q
  have e : signedTag H s ∘ q' = q := by
    funext i; dsimp [q',signedTag]; rw [← S.mirror_mul, mul_inv_cancel, S.mirror_one]
  let y := move s.ortho⁻¹ x
  have e' : move s.ortho y = x := by ext1 i; simp [y]
  have hy := move_in s.ortho⁻¹ hx
  have he := (signed_front h H A s hy q').trans (eqs n q' y hy).symm
  rw [e, ← show y = move s.ortho⁻¹ x from rfl, e'] at he
  exact he

def moveCLM (s : Ortho) : Points n →L[ℝ] Points n := LinearMap.toContinuousLinearMap {
    toFun := move s
    map_add' x y := PiLp.ext fun i => (Ortho.motion s).map_add (x i) (y i)
    map_smul' c x := PiLp.ext fun i => (Ortho.motion s).map_smul c (x i) }

theorem move_direction (s : Ortho) (i : Fin n) (b : Axis) :
    moveCLM s (direction i b) = ∑ a : Axis, s.val a b • direction i a := by
  ext j k
  change Ortho.move s (direction i b j) k =
    PiLp.proj (𝕜 := ℝ) 2 (fun _ => ℝ) k
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ => E4) j (∑ a : Axis, s.val a b • direction i a))
  rw [map_sum, map_sum]; simp only [map_smul, PiLp.proj_apply, smul_eq_mul]
  by_cases e : j = i
  · subst j; simp [direction, Ortho.move]
  simp [direction, e, Ortho.move, M4.move]

theorem gradient_move (s : Ortho) (i : Fin n) (b : Axis) (f : Points n → ℂ) (x : Points n)
    (h : DifferentiableAt ℝ f (move s x)) :
    gradient i b (f ∘ move s) x = ∑ a : Axis, s.val a b • gradient i a f (move s x) := by
  change fderiv ℝ (f ∘ moveCLM s) x _ = _
  change DifferentiableAt ℝ f (moveCLM s x) at h
  rw [fderiv_comp x h (moveCLM s).differentiableAt,(moveCLM s).fderiv,ContinuousLinearMap.comp_apply,
      move_direction,map_sum]; simp only [map_smul]; rfl

theorem gradient_star (i : Fin n) (a : Axis) (f : Points n → ℂ) (x : Points n) :
    gradient i a (fun y => star (f y)) x = star (gradient i a f x) := by rw [gradient,D,fderiv_star]; rfl

theorem compat (hs : S.Smooth) (h : S.Symmetric) (H : S.RealSpin) (P : DiffPlan S)
    (hd : P.Derivatives S) (hu : P.Inclusions S) : P.Orientation H where
  realInc e B := by
    apply real_ext h H; intro n q x hx
    rw [hu.kernels e _ hx, real_front h H B hx, hu.kernels e B hx]
  realDer d a B := by
    apply real_ext h H; intro n q x hx
    rw [hd.kernels _ _ _ hx, hd.kernels d a B hx, ← gradient_star]
    apply GermD
    filter_upwards [(conf_open _).mem_nhds hx] with y hy
    exact real_front h H B hy q
  mirrorInc e s B := by
    apply signed_ext h H s; intro n q x hx
    rw [hu.kernels e _ (move_in _ hx), signed_front h H B s hx, hu.kernels e B hx]
  mirrorDer d b s B := by
    apply signed_ext h H s; intro n q x hx
    let t := signedTag H s ∘ q
    let B' := S.mirror H d s B
    let u : Fin (n+1) → S.Tag := Fin.cons ⟨d,B'⟩ t
    let f z := S.useAt S z u
    let y := move s.ortho x
    have hy : y ∈ conf _ := move_in _ hx
    let m := Ward.here u y 0 (d+1)
    have em (p : S.Field (d+1)) : m p = S.useAt S y (Fin.cons ⟨d+1,p⟩ t) := by
      rw [show m p = _ from Ward.takes u y 0 (d+1) p, Fin.update_cons_zero]; rfl
    change S.useAt S y _ = _
    rw [← em, map_sum]
    have hf := (((S.class_smooth S hs u) y hy).contDiffAt ((conf_open _).mem_nhds hy)).differentiableAt (by simp)
    calc
      _ = ∑ a, s.ortho.val a b • gradient 0 a f y := by
        apply Finset.sum_congr rfl; intro a _
        rw [map_smul, em, hd.kernels d a B' hy,Complex.real_smul]; rfl
      _ = gradient 0 b (f ∘ move s.ortho) x := (gradient_move _ _ b f x hf).symm
      _ = gradient 0 b (fun z => S.useAt S z (Fin.cons ⟨d,B⟩ q)) x := by
        apply GermD
        filter_upwards [(conf_open _).mem_nhds hx] with z hz
        exact signed_front h H B s hz q
      _ = _ := (hd.kernels d b B hx q).symm

theorem answer : YM.Bid.D06 := by
  intro G C S F _ hs h _ P hd hu H
  exact compat hs h H P hd hu
end YM.Work.D06
