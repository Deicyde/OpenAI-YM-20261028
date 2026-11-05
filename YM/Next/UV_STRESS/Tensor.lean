import YM.Next.UV_STRESS.Rates
import YM.Work.A01.Mirror


/-!
# The centered tensor spaces in the stress construction

Real dimensions, signed-cube symmetry, real polar vectors. The divergences
are on the exact observable quotients. In particular the rank hypothesis
we shall need about the free case must itself be proved by a Maxwell producer.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Function Set Filter Analysis Extraction Table Ward Climb Work.A01
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {L : Register G} {T : Table L} {H : T.Hierarchy} {V : DiffPlan T}

def blank (T : Table L) : Fin 0 → T.Tag := Fin.elim0

def expectation (T : Table L) (d : ℕ) : T.Field d →ₗ[ℂ] ℂ := frontRead (blank T) 0 d



def centering (T : Table L) (p : ℕ) : T.Field p →ₗ[ℂ] T.Field p :=
    LinearMap.id - (expectation T p).smulRight (T.unit p)

lemma value_center (v : T.Field 4) : centering T 4 v=v-expectation T 4 v • T.unit 4 := rfl
lemma conf1 : (0:Points (0+1))∈conf _ := fun _ _ _ => @Subsingleton.elim (Fin 1) _ _ _
lemma mean_unit (H : T.Basic) : expectation T 4 (T.unit 4)=1 := by
  rw [expectation,front_eval,T.at_unit H conf1]
  let U : Fin 0 → L.Token := Fin.elim0
  rw [show blank T=T.classTokens ∘ U from Subsingleton.elim ..,T.at_project T H.toSymmetric (fun _ => le_rfl)
    (Points.tail_in conf1)]
  exact H.trivial ..
lemma centers_field (H : T.Basic) (v : T.Field 4) : expectation T 4 (centering T 4 v)=0 := by
  rw [value_center,map_sub,map_smul,mean_unit H,smul_eq_mul,mul_one,sub_self]
lemma const_out (H : T.Basic) : centering T 4 (T.unit 4)=0 := by rw [value_center,mean_unit H,one_smul,sub_self]
lemma mirror_center (H : T.Hierarchy) (v : T.Field 4) (k : Signed) : T.mirror H.spin 4 k (centering T 4 v)=
    centering T 4 (T.mirror H.spin 4 k v) := by
  rw [value_center,value_center,map_sub,map_smul,T.mirror_unit]; congr 2
  have ht := mirror_eval H.laws.toSymmetric H.spin conf1 (Fin.cons ⟨4,v⟩ (blank T)) k
  rw [show Points.move k.ortho 0=0 from ?_,comp_cons,show mirrorTag H.spin k ∘ blank T = blank T from Subsingleton.elim _ _] at ht
  · unfold expectation; simp_rw [front_eval]; exact ht.symm
  ext1 i; simp [Ortho.move,M4.move]
lemma conj_center (H : T.Hierarchy) (v : T.Field 4) : T.conj H.spin 4 (centering T 4 v)=centering T 4 (T.conj H.spin 4 v) := by
  rw [value_center,value_center,map_sub,map_smulₛₗ,T.conj_unit]; congr 2
  have ht := real_eval H.laws.toSymmetric H.spin conf1 (Fin.cons ⟨4,v⟩ (blank T))
  rw [comp_cons, show realTag H.spin ∘ blank T = blank T from Subsingleton.elim _ _] at ht
  unfold expectation; simp_rw [front_eval]; exact ht.symm

private lemma real_mirror (H : T.RealSpin) (d i) (v : T.Field d) (c : ℝ) :
    T.mirror H d i (c • v)=c • T.mirror H d i v := ((T.mirror H d i).restrictScalars ℝ).map_smul _ _
private lemma real_conj (H : T.RealSpin) (d) (v : T.Field d) (c : ℝ) :
    T.conj H d (c • v)=c • T.conj H d v := by
  simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smulₛₗ]; simp

def SymSpace (H : T.RealSpin) : Submodule ℝ T.Stress where
  carrier := {B | (∀ i j,B i j=B j i) ∧ (∀ i j, T.conj H 4 (B i j)=B i j) ∧ RawTensor H B}
  zero_mem' := by
    simp [RawTensor]
  add_mem' := by
    rintro B D ⟨h,g,f⟩ ⟨hp,hg,hf⟩
    refine ⟨fun i j => congr_arg₂ (fun a b : T.Field 4 => a+b) (h i j) (hp i j),fun i j => ?_, fun k i j => ?_⟩
    · simp [g,hg]
    simp only [Pi.add_apply, map_add,f k i j,hf k i j,smul_add, Finset.sum_add_distrib]
  smul_mem' := by
    rintro c B ⟨hp,hg,hf⟩
    refine ⟨fun i j => congr_arg (c • ·) (hp i j),fun i j => ?_,fun k i j => ?_⟩
    · simp only [Pi.smul_apply,real_conj,hg]
    simp only [Pi.smul_apply, real_mirror,hf k i j, Finset.smul_sum]; exact Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => smul_comm _ _ _

def KernelSpace (H : T.RealSpin) : Submodule ℝ T.Stress where
  carrier := {B | B∈SymSpace H ∧ ∀ i j, expectation T 4 (B i j)=0}
  zero_mem' := ⟨Submodule.zero_mem _,fun i j => map_zero _⟩
  add_mem' := fun {_ _} ⟨A,B⟩ ⟨C,D⟩ => ⟨Submodule.add_mem _ A C,fun i j => by simp [B,D]⟩
  smul_mem' := fun c {B} ⟨A,h⟩ => ⟨Submodule.smul_mem _ _ A,fun i j => by
    simp only [Pi.smul_apply, RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,h, smul_zero]⟩

lemma kernel_mem {H : T.RealSpin} {J : T.Stress} : J∈KernelSpace H ↔ J∈SymSpace H ∧ ∀ i j, expectation T 4 (J i j)=0 := Iff.rfl
lemma sym_mem {H : T.RealSpin} {J : T.Stress} : J∈SymSpace H ↔ (∀ i j,J i j=J j i) ∧ (∀ i j,T.conj H 4 (J i j)=J i j) ∧ RawTensor H J := Iff.rfl

abbrev PolarFields (T : Table L) := Axis → T.Field 5

def Vectors (H : T.RealSpin) : Submodule ℝ (PolarFields T) where
  carrier := {v | (∀ i, T.conj H 5 (v i)=v i) ∧ (∀ k i, T.mirror H 5 k (v i)=∑ j : Axis,(↑(k.matrix j i):ℂ) • v j)}
  zero_mem' := by simp
  add_mem' := by
    rintro B D ⟨g,f⟩ ⟨hg,hf⟩
    simp only [mem_setOf_eq,Pi.add_apply, map_add, f,hf,g,hg, smul_add, Finset.sum_add_distrib]
    simp
  smul_mem' := by
    rintro c B ⟨A,h⟩
    refine ⟨fun i => by simp [real_conj,A], fun k i => ?_⟩
    simp only [Pi.smul_apply, real_mirror,h,Finset.smul_sum]; exact Finset.sum_congr rfl fun i _ => smul_comm ..

/-- Real finite tensor divergence. -/
def rayDiv (P : DiffPlan T) : T.Stress →ₗ[ℂ] PolarFields T where
  toFun B i := ∑ j, P.deriv 4 j (B j i)
  map_add' B Q := by ext1 i; simp [Finset.sum_add_distrib]
  map_smul' c Q := by ext1 i; simp [Finset.smul_sum]

lemma vector_div (H : T.RealSpin) (h : V.Orientation H) {B : T.Stress} (hp : B∈SymSpace H) : rayDiv V B∈Vectors H := by
  obtain ⟨_,hr,hB⟩ := hp
  constructor
  · intro i; change T.conj H 5 (∑ j, V.deriv 4 j (B j i))=_; rw [map_sum]; simp_rw [h.realDer,hr]; rfl
  intro k i
  rw [eps_column]
  change T.mirror H 5 k (∑ j, V.deriv 4 j (B j i))= (↑_:ℂ) • ∑ j,V.deriv 4 j (B j (k.perm i))
  rw [map_sum, ← Equiv.sum_comp k.perm (fun j => V.deriv 4 j (B j (k.perm i))), Finset.smul_sum]
  apply Finset.sum_congr rfl; intro j _
  rw [h.mirrorDer, tensor_column hB, eps_column, map_smul, smul_smul]
  congr 1; rw [Complex.ofReal_mul, ← mul_assoc, ← Complex.ofReal_mul,eps_self,Complex.ofReal_one,one_mul]

def currentDiv (V : DiffPlan T) (H : T.RealSpin) (ho : V.Orientation H) : ↑(KernelSpace H) →ₗ[ℝ] ↑(Vectors H) :=
    (((rayDiv V).restrictScalars ℝ).comp (KernelSpace H).subtype).codRestrict (Vectors H)
      (fun v => vector_div H ho (kernel_mem.mp v.property).1)

lemma linear_cons (V : DiffPlan T) (H : T.RealSpin) (ho : V.Orientation H) (v : KernelSpace H) :
    currentDiv V H ho v = 0 ↔ Conserved V H v.val := by
  obtain ⟨h,g,r⟩ := (show v.val∈SymSpace H from (kernel_mem.mp v.property).1)
  exact ⟨fun p => ⟨h,g,fun i => congr_fun (congr_arg Subtype.val p) i⟩,
    fun p => Subtype.ext (funext p.divergence)⟩
end YM.Next.UVStress
