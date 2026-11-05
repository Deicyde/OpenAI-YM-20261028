import YM.Next.RANK.Matrices
import YM.Next.RANK.Rim


/-! Use readout in exact weights. Distinguished vertex transforms on k lattice
may not append arbitrary normalized limits of selected fields. Calibration comparison
needed as ACTUAL linear map and operator estimate (not supplied here). -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Perch
open Lattice Wilson RG Labels Price Normal Function Configuration Beamer Rise MvPolynomial Finset Filter
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {d : ℕ} {V Z : Type*}

def jets (w : V → ℕ) (ρ : ℂ) : poly V →ₐ[ℂ] poly V := MvPolynomial.aeval (fun i => MvPolynomial.C (ρ^w i)*MvPolynomial.X i : V→ poly V)

lemma jets_as (w : V → ℕ) (ρ : ℂ) (i : V →₀ ℕ) (b : ℂ) : jets w ρ (monomial i b) = ρ^(Finsupp.weight w i) • monomial i b := by
  rw [← MvPolynomial.C_mul',monomial_eq]
  unfold jets; rw [map_mul,aeval_C]; unfold Finsupp.prod
  simp only [map_prod,map_pow,aeval_X,mul_pow,prod_mul_distrib, MvPolynomial.algebraMap_eq]; simp only [← map_pow,← map_prod]
  rw [show ∏ j∈i.support,(ρ ^ w j) ^ (i j)= ρ^(Finsupp.weight w i) by
    simp_rw [← pow_mul, prod_pow_eq_pow_sum, Finsupp.weight_apply,Finsupp.sum, nsmul_eq_mul,Nat.cast_id]; simp_rw [mul_comm]]; ring

lemma jets_coeff (p : poly V) (w : V → ℕ) (ρ : ℂ) (i : V →₀ ℕ) : coeff i (jets w ρ p)=ρ^(Finsupp.weight w i)*coeff i p := by
  induction p using MvPolynomial.induction_on' with
  | monomial u x => rw [jets_as,coeff_smul]; by_cases he : u=i
                    · rw [he]; rfl
                    simp [he, smul_eq_mul, coeff_monomial]
  | add p q hp hq => simp [hp,hq,mul_add]
lemma jets_keep (p : poly V) (w : V → ℕ) (ρ : ℂ) (d : ℕ) : trim (jets w ρ p) w d = jets w ρ (trim p w d) := by
  ext i; simp only [trim_coeff,jets_coeff]; split_ifs <;> simp

-- compatibility with thaw before embedding in enlarged coords
lemma peel (ρ : ℂ) (v : poly (Key G)) : jets (V:=KeyIn G d⊕V) bear ρ (rename Sum.inl (boundKey G d v))= rename Sum.inl (boundKey G d (jets Labels.generation ρ v)) := by
  let r := rename (Sum.inl : KeyIn G d → KeyIn G d⊕V) (R:=ℂ)
  let B := r.comp (boundKey G d)
  apply DFunLike.congr_fun (f:=(jets bear ρ).comp B) (g:=B.comp (jets Labels.generation ρ))
  ext1 i; simp only [jets,B,r,AlgHom.comp_apply,aeval_X,map_mul,boundKey,aeval_C,MvPolynomial.algebraMap_eq,rename_C]
  split_ifs <;> simp [bear]

lemma pure_weight (ρ : ℝ) (F : C.label d) :
    ((C.labels.level d).coords.symm (weightTag C d ρ F)).val=jets Labels.generation (ρ:ℂ) ((C.labels.level d).coords.symm F).val := by
  let P:= C.labels.level d
  let s := P.coords.symm
  let M:=weightTag C d ρ
  let T := Labels.localFields G d
  have hv (i) : M (P.coords (P.basis i)) = ((ρ:ℂ)^(P.grades i).1) • P.coords (P.basis i) := by
    rw [P.coords_basis]; ext1 j
    by_cases h : i=j
    · rw [h]; rfl
    simp [M,P,weightTag,Pi.single_eq_of_ne (Ne.symm h)]
  have ht (i : P.Index) : jets Labels.generation (ρ:ℂ) (P.basis i).val=((ρ:ℂ)^(P.grades i).1) • (P.basis i).val := by
    ext j; rw [jets_coeff, coeff_smul]; by_cases h : coeff j (P.basis i).val=0
    · simp [h]
    have he := (pure_grade _ _).1 (P.pure i) h; rw [Labels.weight_slot] at he
    rw [show Finsupp.weight Labels.generation j=(P.grades i).1 from congr_arg Prod.fst he]; rfl
  have he : T.subtype.comp (s.toLinearMap.comp M) = (jets Labels.generation (ρ:ℂ)).toLinearMap.comp (T.subtype.comp s.toLinearMap) := by
    apply (P.basis.map P.coords).ext; intro i; simp only [Module.Basis.map_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hv, map_smul]; change Submodule.subtype _ _=jets Labels.generation (ρ:ℂ) _; simp only [s, LinearEquiv.symm_apply_apply]; exact (ht _).symm
  exact LinearMap.congr_fun he F

lemma cycles {V : Type*} (w : V → ℕ) (ρ : ℂ) (h : ρ≠0) (p : poly V) : jets w ρ⁻¹ (jets w ρ p)=p := by
  ext i; rw [jets_coeff,jets_coeff,inv_pow,← mul_assoc,inv_mul_cancel₀ (by exact pow_ne_zero _ h),one_mul]

lemma spaced (d : ℕ) (f : V → Address G) (ρ : ℝ) (P : Normal.poly V) :
    exchange (features d f ρ) P=jets Configuration.bear ((ρ:ℂ)⁻¹) (exchange (features d f 1) P) := by
  let M := jets (V:=KeyIn G d⊕V) Configuration.bear ((ρ:ℂ)⁻¹)
  have he : exchange (features d f ρ)= M.comp (exchange (features d f 1)) := by
    ext1 i; rw [AlgHom.comp_apply, exchange_x,exchange_x]; unfold features
    simp only [_root_.map_add, _root_.map_sum, Normal.glyph, Finsupp.linearCombination_single, M, jets,map_smul, aeval_X]
    congr 1
    · refine sum_congr rfl fun j _ => ?_
      simp only [MvPolynomial.C_mul', Beamer.fixedKey, Beamer.arbor,Pi.smul_apply,smul_eq_mul,one_pow, inv_one,one_mul,
        Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow,smul_smul, Configuration.bear,Sum.elim_inl, inv_pow]; rw [mul_comm]
    simp [MvPolynomial.C_mul',Configuration.bear]
  exact DFunLike.congr_fun he P

-- At scale 1 these are unweighted (kpc) cell tests after removing t and g.
-- residual V variables never on a low jet. Tests leave correction mask unaffected
-- and are imposed before varying radii/dealing with failed mask.
def Verdict (f : V → Address G) (d : ℕ) (P : Normal.poly V) (F : Label G d) : Prop :=
    Rise.trim (exchange (features d f 1) P) Configuration.bear d=rename Sum.inl (thawKey F)

lemma aligned (f : V → Address G) (ρ : ℝ) (hp : 0<ρ) {k N p : ℕ} {v u : C.label d} {read : C.label d →ₗ[ℂ] C.label d} (h : Solves C ρ d k N p read v u)
    (P : Normal.poly V) (he : Verdict f d P ((C.labels.level d).coords.symm ((C.labels.level d).scaled (shrink C k N p) (read u)))) :
    Rise.trim (exchange (features d f ρ) P) Configuration.bear d=rename Sum.inl (thawKey ((C.labels.level d).coords.symm v)) := by
  unfold Solves at h
  rw [spaced d _ ρ,jets_keep,he,h,thawKey,pure_weight,← peel, cycles]; rfl
  exact Complex.ofReal_ne_zero.mpr hp.ne'
end YM.Next.Rank.Perch
