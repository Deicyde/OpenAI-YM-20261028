import YM.OPE.Orbits.Fresh

/-! Real homogeneous-complement basis simultaneously across horizons. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Orbits.Reader
open Function Set Submodule
open scoped Topology ContDiff Matrix.Norms.Frobenius Classical BigOperators
section Linear
variable {V I:Type}[AddCommGroup V][Module ℂ V][Module ℝ V][IsScalarTower ℝ ℂ V][Fintype I]
    (C : V →ₛₗ[starRingEnd ℂ] V)(he:Function.Involutive C) (f:I→V)(hf:∀ i, C (f i)=f i)

private lemma split_c (x:V):x = (2:ℂ)⁻¹ • (x+C x) + Complex.I • (((2:ℂ)*Complex.I)⁻¹ • (x-C x)) := by
     rw [smul_smul, mul_inv_rev,← mul_assoc,mul_inv_cancel₀ Complex.I_ne_zero,one_mul,← smul_add,add_comm (x+_),sub_add_add_cancel, ← two_smul ℂ, inv_smul_smul₀ two_ne_zero]
include hf he
private lemma spans_c (hs:∀ x:V,C x=x→x∈ Submodule.span ℝ (Set.range f)): ⊤ ≤ Submodule.span ℂ (Set.range f):=by
     intro p hh; have hx:=split_c C p
     have hco : Submodule.span ℝ (Set.range f) ≤ (Submodule.span ℂ (Set.range f)).restrictScalars ℝ:= Submodule.span_le.mpr (fun _ h=> Submodule.subset_span h)
     rw [hx]; apply Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_) <;>
        exact hco (hs _ (by simp only [map_smulₛₗ,map_inv₀,map_mul,map_ofNat,Complex.conj_I, map_add,map_sub,he p,mul_neg, inv_neg, neg_smul,← smul_neg,neg_sub, add_comm]))

lemma independent_c (hi:LinearIndependent ℝ f): LinearIndependent ℂ f :=Fintype.linearIndependent_iff.mpr fun z hz i => by
     have hC: (∑ j, ((starRingEnd ℂ) (z j)) • f j) = 0:= by simpa only [map_sum,map_smulₛₗ,hf,map_zero] using congr_arg C hz
     have hsum (c:I→ℝ)(he:∑ j,((c j:ℝ):ℂ) • f j=0):c i=0:= Fintype.linearIndependent_iff.mp hi c (by simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; exact he) i
     have hstar(j:I):(starRingEnd ℂ) (z j) = ((z j).re:ℂ)-((z j).im:ℂ)*Complex.I  := by
        conv_lhs=> rw [← Complex.re_add_im (z j)]; simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,mul_neg]
        exact (sub_eq_add_neg ..).symm
     have hR : (z i).re=0 := hsum (fun j=>(z j).re) (?pR)
     case pR=>
        have he(z:ℂ): z + (starRingEnd ℂ) z=(2:ℂ)*(z.re:ℂ):=by apply Complex.ext <;> simp <;> ring
        have hf(j): z j • f j+ (starRingEnd ℂ) (z j) • f j=(2:ℂ) • (((z j).re : ℂ) • f j) := by rw [← add_smul,he,mul_smul]
        calc ∑ j, ((↑((z j).re:ℝ)):ℂ) • f j = (2:ℂ)⁻¹ • ((∑ j,z j • f j)+∑ j,(starRingEnd ℂ) (z j) • f j) := by
                    rw [← Finset.sum_add_distrib]; simp_rw [hf,← Finset.smul_sum,inv_smul_smul₀ (two_ne_zero (α:=ℂ))]
             _ = 0 := by rw [hz,hC,add_zero,smul_zero]
     have hI : (z i).im=0:= hsum (fun j=>(z j).im) (?pI)
     case pI=>
        let θ:=(2:ℂ)*Complex.I; have ht:θ≠0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
        have hF(j:I):z j • f j - (starRingEnd ℂ) (z j) • f j = θ • (((z j).im:ℂ) • f j):=by
          rw [smul_smul,← sub_smul,hstar]; congr 1; conv_lhs => lhs; rw [← Complex.re_add_im (z j)]
          unfold θ; ring -- likely second occurrences issue
        calc ∑ j, ((↑((z j).im:ℝ)):ℂ) • f j = θ⁻¹ • ((∑ j,z j • f j)-∑ j,(starRingEnd ℂ) (z j) • f j) := by
                    rw [← Finset.sum_sub_distrib]; simp_rw [hF,← Finset.smul_sum,inv_smul_smul₀ ht]
             _ = 0:= by rw [hz,hC,sub_zero,smul_zero]
     exact Complex.ext hR hI
include he
omit [Fintype I] hf in
lemma basis_exists_c [FiniteDimensional ℂ V] (E:V→ₗ[ℝ] V) (hE:∀v, E v=C v): ∃ n:ℕ, Nonempty {b: Module.Basis (Fin n) ℂ V // ∀ i,C (b i) = b i} :=by
    classical
    let U₀:=LinearMap.ker (E-LinearMap.id)
    let U:= (U₀ : Submodule ℝ V)
    letI : FiniteDimensional ℝ V:= Module.Finite.trans ℂ _
    letI : FiniteDimensional ℝ U:= inferInstanceAs (FiniteDimensional ℝ ↥U₀)
    letI : Module.Free ℝ U:= Module.Free.of_divisionRing ℝ U
    let b:=Module.finBasis ℝ U; let g:=U.subtype ∘ b; let n:=Module.finrank ℝ ↥U
    have hU(i): C (g i) =g i:= by rw [← hE,← sub_eq_zero]; exact (b i).prop
    have hu: LinearIndependent ℝ g:= b.linearIndependent.map' _ (Submodule.ker_subtype _)
    let h₁:=independent_c C he g hU hu;
    have h₂ : ⊤ ≤ span ℂ (range g):= spans_c C he g hU (fun p h=>by
        have h:((E - LinearMap.id : V→ₗ[ℝ] V) p)=0:= by rw [LinearMap.sub_apply,LinearMap.id_apply,hE,h, sub_self]
        let q:U:=⟨p,h⟩
        have hp:p∈span ℝ (range g):=by
            rw [show p=U.subtype q from rfl,← b.sum_repr q,map_sum]
            apply _root_.sum_mem; intro i hi; rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i))
        exact hp)
    refine ⟨n,⟨Module.Basis.mk h₁ h₂,?_⟩⟩; intro i; simp only [Module.Basis.mk_apply,hU]
end Linear

variable {G:Gauge}{L:Register G}{S:Table L}{Q:DiffPlan S}{ρ:S.RealSpin}{X:S.Rotation} (R:Orbits.Reader Q X ρ)
def spinC (m):R.stratum m →ₛₗ[starRingEnd ℂ] R.stratum m:= ((S.conj ρ m).domRestrict (R.stratum m)).codRestrict _ fun v=>R.bar_mem m v.val v.prop
lemma involution (m):Involutive (R.spinC m):= fun p=> Subtype.ext (S.reflect_star ρ m p.val)
def spinR (m): R.stratum m →ₗ[ℝ] R.stratum m :=
    { (R.spinC m).toAddHom with
       map_smul' := fun r v=> (by apply Subtype.ext; exact (conjugateR ρ m).map_smul r v.val) }

def fixedSpace m:= LinearMap.ker (R.spinR m - LinearMap.id)
local instance finite_s(m): FiniteDimensional ℝ (R.stratum m):= Module.Finite.trans ℂ _
lemma findBasis(m):∃ n:ℕ, Nonempty {b:Module.Basis (Fin n) ℂ (R.stratum m)//∀ i,R.spinC m (b i)= b i}:= by
    apply basis_exists_c _ (R.involution _ ) (R.spinR m) (fun i=>rfl) -- rfl
abbrev channels m:= Fin (R.findBasis m).choose

def basis (m:ℕ): Module.Basis (R.channels m) ℂ (R.stratum m):= (Classical.choice (R.findBasis m).choose_spec).val
lemma needle_real (m) (j:R.channels m): S.conj ρ m (R.basis m j).val=(R.basis m j).val := congr_arg Subtype.val ((Classical.choice (R.findBasis m).choose_spec).prop j)
lemma needle_in (m)(i:R.channels m)(k:Ortho):X.act m k (R.basis m i).val ∈ R.stratum m:= R.turn_mem m _ k (SetLike.coe_mem _)
-- field truncated basis already `reconstruct`; check equality with all direct kernel values later
end YM.OPE.Orbits.Reader
