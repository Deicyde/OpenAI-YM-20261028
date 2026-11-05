import YM.FullVolume.Maintain

/-! Linear algebra of probes in finite dimension. Explicitly state
purchases of rank lower and upper *on the same varying rows*. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Function Set Filter Metric MeasureTheory Lattice RG Wilson Extraction Extraction.Lease Difference Gaps Cells Next.Rank Next.Rank.Market Push.RelayDifference
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n m : ℕ}

abbrev Size (n:ℕ) := Fin n→ℂ
def arrange (f:Fin n→E) : Size n→ₗ[ℂ] E:= (Pi.basisFun _ _).constr ℂ f
lemma ordered (f : Fin n → E) (x:Size n): arrange f x=∑ i,x i • f i:= by simp [arrange]
lemma ordered_at (f:Fin n→E) (j:Fin n): arrange f ((Pi.basisFun ℂ _) j) = f j:= Module.Basis.constr_basis ..
lemma capacity (x: Size n) (f : Fin n→E) (A:ℝ) (h:∀ i, ‖f i‖≤A): ‖arrange f x‖≤ n*‖x‖*A:= by
  rw [ordered]; apply (norm_sum_le ..).trans ((Finset.sum_le_sum (g:= fun _ => ‖x‖ * A) (fun i _=> by rw [norm_smul]; exact mul_le_mul (norm_le_pi_norm x i) (h i) (norm_nonneg _) (norm_nonneg _))).trans_eq ?_)
  simp [mul_assoc]
lemma firm {g:Fin n → Size m} (h:Injective (arrange g)):
    ∃ δ M : ℝ, 0<δ ∧ 0<M ∧ ∀ L: Size n →ₗ[ℂ] Size m,
      (∀ i,‖L ((Pi.basisFun ℂ _) i)-g i‖ ≤ δ) →
        ∀ x, ‖x‖ ≤ M*‖L x‖ := by
  obtain ⟨K,hK,k⟩:= LinearMap.exists_antilipschitzWith _ (LinearMap.ker_eq_bot.mpr h)
  let K':= (K:ℝ); let δ:ℝ:= (2*K'*(n+1))⁻¹
  have ht:0<K':=by exact_mod_cast hK
  refine ⟨δ,2*K',by unfold δ; positivity,by positivity,fun L h' x=>?_⟩
  let y:=(L-arrange g)
  have hy:y=arrange (fun i=> L ((Pi.basisFun ℂ _) i)-g i):=by apply (Pi.basisFun ..).ext; intro i; change L _ - arrange g _=_; rw [ordered_at g, ordered_at]
  have hp: ‖L x-arrange g x‖ ≤ n*‖x‖*δ:=by change ‖y x‖ ≤ _; rw [hy]; exact capacity x _ _ h'
  have hb : 0<δ:=by unfold δ; positivity
  have hv : ‖x‖≤K'*‖arrange g x‖:= ZeroHomClass.bound_of_antilipschitz (arrange g) k x
  have hg := hp; rw [norm_sub_rev] at hg
  have he: K'*(n*‖x‖*δ)≤‖x‖/2:= by
    calc
      _ ≤ K'*(((n:ℝ)+1)*‖x‖*δ) := by gcongr; linarith
      _ = _ := by unfold δ; field_simp
  have hx:= norm_sub_norm_le (arrange g x) (L x)
  nlinarith only [hg,hx,mul_le_mul_of_nonneg_left (hx.trans hg) ht.le,he,hv]

variable [FiniteDimensional ℂ E]
lemma rank_upper {a: E →L[ℂ] E} {f: Fin n→E} {A:ℝ} (h:∀ i, ‖f i‖ ≤ A) {M L:ℝ}(hM:‖a‖ ≤ M) (_hP:0≤L) (g:E→ₗ[ℂ] Size m)
    (h':∀ x: Size n, ‖x‖≤ L*‖g (a (arrange f x))‖) (hp: Module.finrank ℂ (LinearMap.range a.toLinearMap) ≤ n) (hA: 0 ≤ A):
    ∀ x:E, ‖a x‖ ≤ M*n*A*L*‖g (a x)‖:= by
  let F:= (LinearMap.rangeRestrict a.toLinearMap).comp (arrange f)
  have hf: Injective F:=by
    apply LinearMap.ker_eq_bot.mp; apply LinearMap.ker_eq_bot'.mpr; intro x hx
    have he: a (arrange f x)=0:= congr_arg Subtype.val hx
    simpa [he] using h' x
  have hs : Surjective F:= (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Nat.le_antisymm (LinearMap.finrank_le_finrank_of_injective hf) (by simpa [Size] using hp))).1 hf
  intro x
  obtain ⟨t,ht⟩:= hs (a.toLinearMap.rangeRestrict x)
  have ht: a (arrange f t)=a x:= congr_arg Subtype.val ht
  rw [←ht]; refine (a.le_opNorm _).trans ((mul_le_mul hM (capacity t f A h) (norm_nonneg _) ((norm_nonneg a).trans hM)).trans ?_)
  have hv : 0≤M:= (norm_nonneg a).trans hM
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h' t) (Nat.cast_nonneg _)) hA) hv).trans_eq (by ring)
variable {G:Gauge}{C:Family G}{S:Table C.book}{d:ℕ}(X:Columns C S d)

-- reuse `functional` form from Beam on same columns
private lemma functional (i : Fin X.amount) : ∃ F : (standard C).Field d →ₗ[ℂ] ℂ,
    ∀ x, F x=(X.row i).tests (standard C) X.basis x := by
  let T := standard C
  let n := (X.row i).extra
  let p := (X.row i).expected
  let r (j : Fin n) := X.basis ((X.row i).uses j)
  let v (j : Fin n) : (Maxwell.standard C.labels).Token := ⟨d,T.representative d (r j)⟩
  let F := (T.injectFront v p d).comp (T.representative d)
  refine ⟨F,fun x => ?_⟩
  change T.read p (Fin.cons ⟨d,T.representative d x⟩ v)=T.useAt T p (Fin.cons ⟨d,x⟩ (fun i => ⟨d,r i⟩))
  let H (a : T.Tag) := (⟨a.1,T.representative a.1 a.2⟩ : (Maxwell.standard C.labels).Token)
  change _= T.read p (H ∘ (Fin.cons (α:=fun _ => T.Tag) ⟨d,x⟩ (fun i => ⟨d,r i⟩)))
  congr 1; funext i; refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
lemma true_lower : Injective (arrange (fun j i => focus (X:=X) i j)):=by
  choose V hv using functional X
  let T:= LinearMap.pi V
  have hf: Injective T:= by intro x y H; apply X.full; funext i; dsimp only; rw [←hv,←hv]; exact congr_fun H i
  let B:=(Pi.basisFun ℂ (Fin (X.dim+1))).equiv X.basis (Equiv.refl _)
  have hd : arrange (fun j i => focus (X:=X) i j) = T.comp B.toLinearMap:= by
    apply (Pi.basisFun ..).ext; intro i
    rw [ordered_at (fun j i => focus (X:=X) i j)]; ext j:1; symm
    change V j (B _)=_; rw [show B _= X.basis i from (Pi.basisFun ℂ _).equiv_apply i X.basis (Equiv.refl _) ] -- check
    apply hv
  rw [hd]; exact hf.comp B.injective
end YM.FullVolume
