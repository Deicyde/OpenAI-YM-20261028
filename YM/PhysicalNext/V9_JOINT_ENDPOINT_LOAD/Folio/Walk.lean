import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Itinerary
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.After

/-! # Two-sided counting with jumps of arbitrary length and halos on every visit

Don't introduce a factor exp(s B) about a support hit to recenter to an
endpoint: its rate may belong to another exponential purchase. Same
physical torus even with coincident `site` points.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Folio
open Filter Function Set Lattice RG Wilson Pressure Precision Tree Matrix Finset
open Next.SectorChange Wisps Further.GaussianScalar AnalyticBridge.AnnulusRatioInsertions.Prism
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {I : Type} [Fintype I] {c f : Side} {p : I→Site c} {s C H : ℝ} {r m B : ℕ} {x : Site c} {P : Patch} {S : StepData c f}

def pathWeight (p : I→Site c) (s : ℝ) (n : ℕ) (i : I) (h : Fin n→I) (j : I) := rate (-s) (length p n i h j)
omit [Fintype I] in
lemma path_succ (n : ℕ) (i : I) (h : Fin (n+1)→I) (j : I) :
    pathWeight p s (n+1) i h j=rate (-s) (separation (p i) (p (h 0))) * pathWeight p s n (h 0) (Fin.tail h) j := by
  simp only [pathWeight,length,rate,Nat.cast_add,mul_add,Real.exp_add]
omit [Fintype I] in
lemma path_cons (n : ℕ) (i a : I) (h : Fin n→I) (j : I) :
    pathWeight p s (n+1) i (Fin.cons a h) j=rate (-s) (separation (p i) (p a)) * pathWeight p s n a h j := by rw [path_succ,Fin.cons_zero,Fin.tail_cons]
omit [Fintype I] in
lemma map_cons (n : ℕ) (i a : I) (h : Fin n→I) (j : I) :
    sectionMap p r (n+1) i (Fin.cons a h) j=From I p r i ∪ sectionMap p r n a h j := by rw [sectionMap,Fin.cons_zero, Fin.tail_cons]
private lemma roll (n : ℕ) (w : (Fin (n+1) → I) → ℝ) : ∑ h, w h = ∑ i:I,∑ t,w (Fin.cons i t) := by rw [← Equiv.sum_comp (Fin.consEquiv (fun _ => I)), Fintype.sum_prod_type]; rfl

variable (hC : 0≤C) (h : ∀ i:I, (∑ j,rate (-s) (separation (p i) (p j)))≤C)
include hC h
lemma forwards (n : ℕ) (i : I) : (∑ h',∑ j,pathWeight p s n i h' j) ≤ C^(n+1) := by
  induction n generalizing i with
  | zero => simpa only [pathWeight,length,sum_const,card_univ,Fintype.card_pi_const, Fintype.card_fin,pow_zero,one_smul,Nat.zero_add,pow_one] using! h i
  | succ n ih =>
    rw [roll,pow_succ']; simp_rw [path_cons, ← Finset.mul_sum]
    exact (Finset.sum_le_sum fun a _=>mul_le_mul_of_nonneg_left (ih a) (rate_pos ..).le).trans (((Finset.sum_mul ..).symm.le).trans (mul_le_mul_of_nonneg_right (h i) (pow_nonneg hC _)))

lemma byOrigin (hc : ((Finset.univ.filter fun i:I => x∈From I p r i).card:ℝ) ≤ H) (n : ℕ) :
    let f i h j := if x∈sectionMap p r n i h j then pathWeight p s n i h j else 0
    (∑ i,∑ h',∑ j,f i h' j) ≤ (n+2:ℝ)*H*C^(n+1) := by
  intro f
  have hF (n : ℕ) : (∑ i,∑ (h' : Fin n→I),∑ j, if x∈From I p r i then pathWeight p s n i h' j else 0) ≤ H*C^(n+1) := by
    simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero, ← Finset.sum_filter]
    refine (Finset.sum_le_sum (g:=fun _=>C^(n+1)) fun i _=>forwards hC h n i).trans ?_
    rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hc (pow_nonneg hC _)
  induction n with
  | zero =>

    let f₀ (i j : I) := if x∈From I p r i then pathWeight p s 0 i Fin.elim0 j else 0
    have hp : ∑ i,∑ j,f₀ i j ≤ H*C := by simpa only [pathWeight,f₀,sum_const,card_univ,Fintype.card_pi_const, Fintype.card_fin,pow_zero, one_smul,zero_add,pow_one,length] using hF 0
    have hb (i j : I) : (∑ h':Fin 0→I, f i h' j) ≤ f₀ i j + f₀ j i := by
      unfold f sectionMap pathWeight length; simp only [sum_const,card_univ,Fintype.card_pi_const,pow_zero,one_smul,Finset.mem_union]
      have he := rate_pos (-s) (separation (p i) (p j))
      unfold f₀ pathWeight length
      rw [separation_comm (p j) (p i)]; split_ifs <;> first | linarith | tauto
    rw [Nat.cast_zero,zero_add,Nat.zero_add,pow_one]
    simp_rw [Finset.sum_comm (s:=univ (α:=Fin 0→I)) (t:=univ (α:=I))]
    apply ((Finset.sum_le_sum fun i _=>Finset.sum_le_sum fun j _=>hb i j).trans ?_)
    simp_rw [Finset.sum_add_distrib]
    have hh : ∑ i,∑ j,f₀ j i ≤ H*C := (Finset.sum_comm ..).trans_le hp
    linarith only [hp,hh]
  | succ n ih =>
    let G (a:I) (h':Fin n→I) j := if x∈sectionMap p r n a h' j then pathWeight p s n a h' j else 0
    have hg a : 0 ≤ ∑ h',∑ j,G a h' j := Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>by unfold G; split; exact (rate_pos ..).le; exact le_rfl
    have hi : ∑ a,∑ h',∑ j,G a h' j ≤ _ := ih
    let Y := From I p r
    let q i a := rate (-s) (separation (p i) (p a))
    let w := pathWeight p s (n+1)
    let v i a h' j := if x∈Y i then w i (Fin.cons a h') j else 0
    have hv : ∑ i,∑ a,∑ h',∑ j,v i a h' j ≤ H*C^(n+1+1) := by simpa only [roll (I:=I) (n:=n)] using! hF (n+1)
    have hb i a h' j : f i (Fin.cons a h') j ≤ v i a h' j + q i a * G a h' j := by
      have hp:= mul_pos (rate_pos (-s) (separation (p i) (p a))) (show 0<pathWeight p s n a h' j from rate_pos ..)
      unfold f v G q w Y; simp only [map_cons,Finset.mem_union,path_cons]; split_ifs <;> first | linarith | tauto
    simp_rw [roll (I:=I) (n:=n)]
    apply (Finset.sum_le_sum fun i _=>Finset.sum_le_sum fun a _=>Finset.sum_le_sum fun h' _=>Finset.sum_le_sum fun j _=>hb i a h' j).trans ?_
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]; rw [Finset.sum_comm (f:=fun i a=>q i a * ∑ h',∑ j,G a h' j)]
    have hd a : ∑ i,q i a ≤ C := by simpa only [q,separation_comm] using h a
    have hc := (Finset.sum_le_sum (s:=univ) fun a _=>mul_le_mul_of_nonneg_right (hd a) (hg a)).trans_eq (Finset.mul_sum ..).symm
    have he := hc.trans (mul_le_mul_of_nonneg_left hi hC)
    simp_rw [← Finset.sum_mul]; apply (add_le_add hv he).trans_eq; push_cast; ring

omit hC h

def heads (P : Patch) (r : ℕ) := ((r+r+1)^4:ℕ)*((P.L.val^4 * Fintype.card Axis:ℕ):ℝ)
lemma heads_cost (hP : S.patch=P) (x : Site c) (r : ℕ) : ((univ.filter fun i:Bond f => x ∈ From _ (home S) r i).card:ℝ) ≤ heads P r := by
  let H := halo r {x}; let w (j : Site c) := if j ∈ H then (1:ℝ) else 0
  have hs i : x∈From _ (home S) r i ↔ home S i∈H := by simp [H,halo_spec,separation_comm x]
  have ht := Corona.halo_size ({x}:Support c) r; rw [Finset.card_singleton,one_mul] at ht

  have he : (∑ j,w j) ≤ ((r+r+1:ℕ)^4:ℝ) := by simpa only [w,←sum_filter,sum_const,nsmul_eq_mul, mul_one,filter_mem_eq_inter, Finset.univ_inter,Nat.cast_pow] using (Nat.cast_le (α:=ℝ).mpr ht)
  rw [← hP] -- P counts
  calc
    _ = ∑ i : Bond f,w (home S i) := by simp [w,←hs,sum_boole]
    _ ≤ _ := by simp only [Fintype.sum_prod_type,sum_const,card_univ,nsmul_eq_mul,←Finset.mul_sum,home,Work.F01.sum_parent, site_card,heads]; push_cast; push_cast at he; rw [show S.patch.L=S.ratio.count from rfl]
                convert mul_le_mul_of_nonneg_right he (by positivity : 0≤(S.ratio.count.val:ℝ)^4*Fintype.card Axis) using 1 <;> first | ring | rfl

lemma poured (hP : S.patch=P) (hs : 0<s) (i : Bond f) : (∑ j:Bond f,rate (-s) (separation (home S i) (home S j))) ≤ Breeze.storm P s := by
  rw [Fintype.sum_prod_type]; simp only [sum_const,card_univ,nsmul_eq_mul,← Finset.mul_sum,home]
  rw [Work.F01.sum_parent S.ratio (fun j => rate (-s) (separation (home S i) j)),←hP] -- expression home unfolded
  have he := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Tier.land hs (home S i)) (by positivity : 0≤(Fintype.card (Site S.ratio.count):ℝ))) (by positivity : 0≤(Fintype.card Axis:ℝ))
  unfold Breeze.storm; change _ ≤ Tier.wealth s * ((Fintype.card (Site S.ratio.count):ℝ)*_)
  simp_rw [separation_comm _ (home S i)] at he
  exact he.trans_eq (by ring)
end YM.PhysicalNext.JointLoad.Folio
