import YM.RG08.Prism.Lung

/-! # Expose boiler as ledger from completed square certified against raw liability
 H. consumption, at every regulator. Compatible with enlarging by external probes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Prism
open Filter Lattice RG Wilson Forms Pert.Bulk Isles Camera Glyph Room Exterior Function Finset MvPolynomial Matrix Fold Haze
open scoped Classical ContDiff Topology BigOperators Matrix PowerSeries
variable {I J U R O:Type}[Fintype I][Fintype J][Fintype U][Fintype R][Fintype O]
variable (A:Drum I J U)(E:J⊕U≃R)(t:U→O)
-- mapping to thermostat

def whisk (t:U→O): Matrix U O ℝ:= Matrix.of fun i j=> (Pi.single (t i) 1 : O→ℝ) j
omit [Fintype U] in
lemma whistle [Fintype U] (t:U→O)(x:Cellar O):whisk t *ᵥ x=x ∘ t:=by ext i; simp [mulVec,dotProduct,whisk,Pi.single_apply,ite_mul]
def exposure := A.mean * whisk t
def spend := (whisk t)ᵀ*A.N*whisk t

def rifle :Matrix (J⊕ U) (I⊕O) ℝ:=Matrix.fromBlocks A.v (exposure A t) 0 (whisk t)
def speak : Matrix R (Raw I O) ℝ:= fun i j=> rifle A t (E.symm i) j
omit [Fintype R] in
lemma speak_zone [Fintype R] (x:Cellar (Raw I O)): ((fun i:J=> ((speak A E t) *ᵥ x) (E (.inl i)))=A.v *ᵥ (x ∘ Sum.inl) + A.mean *ᵥ ((x ∘ Sum.inr) ∘ t)) ∧
 ((fun i:U=>((speak A E t) *ᵥ x) (E (.inr i)))= (x ∘ Sum.inr) ∘ t):=by
 simp only [speak,Matrix.mulVec,dotProduct,rifle,Equiv.symm_apply_apply] -- names
 constructor
 · funext i
   have he: exposure A t *ᵥ (x ∘ Sum.inr) = A.mean *ᵥ ((x ∘ Sum.inr) ∘ t):= by rw [exposure,←mulVec_mulVec,whistle]
   change _=(A.v*ᵥ (x ∘ Sum.inl)+A.mean *ᵥ ((x ∘ Sum.inr) ∘ t)) _;rw [←he];simp [mulVec,dotProduct,Fintype.sum_sum_type]
 funext i
 simp only [Fintype.sum_sum_type,fromBlocks_apply₂₁,fromBlocks_apply₂₂,Matrix.zero_apply, zero_mul,sum_const_zero,zero_add];exact congrFun (whistle t (x ∘ Sum.inr)) i

def ember :Matrix (J⊕ U) (J⊕ U) ℝ:=Matrix.fromBlocks A.g 0 0 0
def press :Matrix R R ℝ:=(ember A).submatrix E.symm E.symm
omit [Fintype R] in
lemma steamed (h:A.Flourishes)(i j:R):press A E i j=press A E j i:=by
 have hh : A.gᵀ = A.g := by
   unfold Drum.g
   rw [transpose_mul, transpose_transpose, transpose_mul, A.mirrored h, Matrix.mul_assoc]
 unfold press
 simp only [Matrix.submatrix_apply]
 cases E.symm i with
 | inl i =>
   cases E.symm j with
   | inl j => exact congrFun (congrFun hh j) i
   | inr j => rfl
 | inr i => cases E.symm j <;> rfl
-- structural relation to heat and zeroing
omit [Fintype R] in
lemma brochure (h:A.Flourishes):Relation (morn A.dark (A.direction h) O) (press A E) (speak A E t):=by
 intro i k;simp_rw [morn,Finset.sum_map]; unfold speak rifle press
 rcases hi:E.symm i with a|a <;> rcases hk:E.symm k with b|b <;> simp [hi,hk,Matrix.fromBlocks,ember]
 simp only [Drum.g,Matrix.mul_apply,Finset.sum_mul,transpose_apply];rw [Finset.sum_comm];apply sum_congr rfl;intro j _; apply sum_congr rfl;intro v _;ring
lemma outside (h:A.Flourishes): Abroad (morn A.dark (A.direction h) O).foam (Fold.platen (spend A t) I):=by
 intro i hi;rcases i with a|a
 · exact Fold.perimeter (spend A t) a
 exfalso;simp [morn] at hi

def forges (h:A.Flourishes)(V:Steam.Grain R)(hl:Steam.Eligible V)(hv:waxed V):Peak I O R:={
 theater:=morn _ (A.direction h) O
 K:=heater A.inside O
 P:=fun x y=> Sum.elim (fun i=> Sum.elim (fun j=>A.inside i j) (fun _=>0) y) (fun _=>0) x
 κ:=platen (spend A t) I
 input:=V
 prices:=press A E
 view:=speak A E t
 inside:=A.inside
 outside:=spend A t
 mirror:=A.symmetry h
 inverse:=h.even
 symm:=A.direction h
 present:=rfl
 warm:=rfl
 cold:=rfl
 orientation:={cards:=⟨hv,hl,steamed A E h⟩,boil:=Fold.heat A.inside A.dark (A.symmetry h) (A.direction h) (A.invertible h),deck:=brochure A E t h,perimeter:=outside A t h}
}

omit [Fintype I] in
lemma plane (L:Matrix I J ℝ)(x:Cellar J)(i:I):MvPolynomial.eval x (median L i)=(L*ᵥ x) i:=by simp [median,MvPolynomial.smul_eq_C_mul,mulVec,dotProduct]
omit [Fintype I] in
lemma aim_eval [Fintype I] (L:Matrix I J ℝ)(x:Cellar J)(p:Inn I):MvPolynomial.eval x (twistMean L p)= MvPolynomial.eval (L*ᵥ x) p:=by -- twistMean name
 induction p using MvPolynomial.induction_on with
 | C i=>simp [twistMean]
 | add _ _ ht hh=>rw [map_add,map_add,map_add,ht,hh]
 | mul_X p i hp=>rw [_root_.map_mul,_root_.map_mul,_root_.map_mul,hp];congr 1;rw [twistMean,aeval_X,eval_X];exact (plane L x i)
