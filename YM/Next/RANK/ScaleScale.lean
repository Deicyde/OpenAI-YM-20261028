import YM.Next.RANK.ScaleJet

/-!
# Trimming and factor weights for the calibration (local Key transform)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.LiftMark
open Function Beamer Configuration Normal MvPolynomial Finset Labels Rise Perch
open scoped BigOperators Topology Classical

variable {G : Gauge} {V Z : Type*} {d n : ℕ} {e t : ℝ}

def factors (t : ℂ) : poly V →ₐ[ℂ] poly V := jets (fun _ => 1) t
@[simp] lemma factors_X (t : ℂ) (i : V) : factors t (X i)= C t* X i := by simp [factors,jets]
@[simp] lemma factors_C (t b : ℂ) : factors t (C b)=C (σ:=V) b := by simp [factors,jets]


lemma factorThaw {v : Labels.Label G d} (t : ℂ) : factors t (thawKey v)=boundKey G d (factors t v.val) := by
  apply DFunLike.congr_fun (f:=(factors t).comp (boundKey G d)) (g:=(boundKey G d).comp (factors t))
  ext1 i; simp only [AlgHom.comp_apply, factors_X,boundKey, map_mul,aeval_X, MvPolynomial.aeval_C,MvPolynomial.algebraMap_eq]
  split_ifs <;> simp
lemma weighed (F : Frame G d) (v : F.Coeff) (t : ℝ) : ((F.coords.symm (F.scaled t v)).val)=factors (t:ℂ) (F.coords.symm v).val := by
  have hx (x : Labels.Key G →₀ ℕ) : Finsupp.weight (fun _ : Labels.Key G => 1) x=(Finsupp.weight Labels.bidegree x).2 := by
    rw [weight_slot,Finsupp.weight_apply]; simp
  have hv (i : F.Index) : F.scaled t (F.coords (F.basis i))=(((t^(F.grades i).2:ℝ):ℂ)) • F.coords (F.basis i) :=
    F.scaled_pure _ (F.grades i) (F.pure i)
  apply LinearMap.congr_fun (f:= (Labels.localFields G d).subtype ∘ₗ F.coords.symm.toLinearMap ∘ₗ F.scaled t)
    (g:= (factors (t:ℂ)).toLinearMap ∘ₗ (Labels.localFields G d).subtype ∘ₗ F.coords.symm.toLinearMap)
  apply (F.basis.map F.coords).ext; intro i; simp only [Module.Basis.map_apply,LinearMap.comp_apply]; change Submodule.subtype _ (F.coords.symm (F.scaled t (F.coords _)))= factors _ (F.coords.symm (F.coords _)).val
  rw [hv,map_smul,F.coords.symm_apply_apply]; ext j
  change coeff j ((((t^(F.grades i).2:ℝ):ℂ)) • (F.basis i).val)= _; rw [coeff_smul,factors,jets_coeff,hx]
  by_cases h : j∈ (F.basis i).val.support
  · rw [(pure_grade ..).1 (F.pure i) (mem_support_iff.mp h),Complex.ofReal_pow]; rfl
  rw [MvPolynomial.notMem_support_iff.mp h,mul_zero,smul_zero]
lemma weighed_in (F : Frame G d) (v : F.Coeff) (t : ℝ) :
    thawKey (F.coords.symm (F.scaled t v)) = factors (t:ℂ) (thawKey (F.coords.symm v)) := by rw [factorThaw,thawKey,weighed F v t]

-- `Verdict` residual columns cannot enter after trim.

def key (G : Gauge) (d : ℕ) := fun i : KeyIn G d => Labels.generation i.val

lemma trim_add (w : V → ℕ) (d : ℕ) (p q : poly V) : trim (p+q) w d=trim p w d+trim q w d := by ext i; simp only [coeff_add, trim_coeff,coeff_add]; split_ifs <;> simp
lemma trim_smul (w : V → ℕ) (d : ℕ) (p : poly V) (t : ℂ) : trim (t • p) w d=t • trim p w d := by ext i; simp only [coeff_smul,trim_coeff];split_ifs <;> simp
def level (w : V → ℕ) (d : ℕ) : Module.End ℂ (poly V) where
  toFun p := trim p w d
  map_add' p q := trim_add w d p q
  map_smul' r p := trim_smul w d p r
lemma trim_sub (w : V → ℕ) (d : ℕ) (p q : poly V) : trim (p-q) w d= trim p w d-trim q w d := map_sub (level w d) p q
lemma trim_factor (p : poly V) (w : V → ℕ) (d : ℕ) (t : ℂ) : trim (factors t p) w d=factors t (trim p w d) := by ext i; simp only [factors,trim_coeff,jets_coeff]; split_ifs <;> simp
lemma trim_mono (w : V → ℕ) (d : ℕ) (x : V →₀ ℕ) (t : ℂ) : trim (monomial x t) w d=if Finsupp.weight w x ≤ d then monomial x t else 0 := by
  ext i; rw [trim_coeff]; by_cases hi : i=x
  · subst i; split_ifs <;> simp
  rw [coeff_monomial]; split_ifs <;> simp [coeff_monomial,Ne.symm hi] <;> aesop
lemma trim_rename (f : V → Z) (w : Z → ℕ) (p : poly V) (d : ℕ) : trim (rename f p) w d= rename f (trim p (w ∘ f) d) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u x =>
    rw [trim_mono,rename_monomial,trim_mono]
    have he (u : V →₀ ℕ) : Finsupp.weight w (Finsupp.mapDomain f u)=Finsupp.weight (w∘f) u := by
      induction u using Finsupp.induction_linear with
      | zero => simp
      | add x y h1 h2 => simp [Finsupp.mapDomain_add,h1,h2]
      | single i b => simp [Finsupp.weight_apply]
    rw [he]; split_ifs <;> simp [rename_monomial]
  | add x y h1 h2 => rw [map_add,trim_add,trim_add,h1,h2,map_add]

lemma fine_weight (w : V → ℕ) (p q : poly V) (i) : trim (trim p w i*q) w i=trim (p*q) w i := by
  induction p using MvPolynomial.induction_on' with
  | add x y h1 h2 => rw [trim_add,add_mul,add_mul,trim_add,trim_add,h1,h2]
  | monomial u x =>
    rw [trim_mono]; split_ifs with h; · rfl
    induction q using MvPolynomial.induction_on' with
    | add p q h1 h2 => rw [mul_add,mul_add,trim_add, trim_add,h1,h2]
    | monomial z b => rw [zero_mul,monomial_mul,trim_mono,if_neg]; · ext a; simp only [trim_coeff,coeff_zero]; split_ifs <;> rfl
                      rw [map_add]; omega

-- projection onto Test polynomial coefficients (Drop resid). When lower-weight per i agree before, changes create only heavier terms.
lemma verdict_map {F Q : poly V →ₐ[ℂ] poly Z} (d) (w : Z→ℕ) (h : ∀ i,trim (F (X i)) w d=trim (Q (X i)) w d) (p : poly V) : trim (F p) w d=trim (Q p) w d := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [show F (C a)= C a from F.commutes a, show Q (C a)= C a from Q.commutes a]
  | add p q h1 h2 => rw [map_add,map_add,trim_add,trim_add,h1,h2]
  | mul_X p i hp =>
    rw [map_mul,map_mul, ← fine_weight, hp, mul_comm, ← fine_weight, h,
      mul_comm (trim (Q (X i)) w d),fine_weight,mul_comm (Q p),fine_weight, mul_comm]

-- size of lower projections; don't enlarge amplitudes after integrating
lemma trims (r : ℝ) (ht : 0 ≤ r) (w : V→ℕ) (z : V→ℕ) (d) (x : poly V) : cents (trim x z d) w r≤cents x w r := by
  unfold trim; apply (Rise.collect w ht _ _).trans
  simp only [Rise.tavern]; apply sum_le_sum_of_subset_of_nonneg (filter_subset ..); intro i _ _; positivity

variable (d) (F : V → Beamer.Address G)
def ink (i : V) := ∑ j : KeyIn G d, Finsupp.single j (((Beamer.tester j.val) (F i):ℝ):ℂ)
lemma intern (i : V) : Normal.glyph (features d F 1 i) = rename Sum.inl (exchange (ink d F) (X i)) + X (Sum.inr i) := by
  simp only [features,fixedKey,arbor,Normal.glyph,_root_.map_add,_root_.map_sum, Normal.exchange_x,ink,Finsupp.linearCombination_single,
    Complex.ofReal_one,one_pow,inv_one,one_smul,map_smul,rename_X]
lemma costs (p : poly V) :
    Rise.trim (Normal.exchange (features d F 1) p) bear d =
      rename Sum.inl (Rise.trim (Normal.exchange (ink d F) p) (key G d) d) := by
  rw [← show Rise.trim _ bear d=rename (Sum.inl : KeyIn G d → KeyIn G d ⊕ V) (trim (exchange (ink d F) p) (key G d) d) from trim_rename ..]
  apply verdict_map d _ (Q:=(rename Sum.inl).comp (exchange (ink d F))) ?_ p
  intro i; rw [AlgHom.comp_apply, Normal.exchange_x,intern,trim_add, X,X,trim_mono]
  rw [Finsupp.weight_single]; simp only [one_smul,bear,Sum.elim_inr,Nat.not_succ_le_self,↓reduceIte,add_zero]
end YM.Next.Rank.LiftMark
