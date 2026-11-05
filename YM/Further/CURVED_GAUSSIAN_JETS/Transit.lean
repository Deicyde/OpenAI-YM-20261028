import YM.Further.CURVED_GAUSSIAN_JETS.EllV
import YM.Further.CURVED_GAUSSIAN_JETS.Passengers
/-!
# Reading absolute chain prices through the positive real spectral integral
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Tracks
open Matrix Function Filter Jets Lattice Wilson RG Precision Set MeasureTheory Push.Uniform SectorNext.Vacuum
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {I : Type*} [Fintype I] [DecidableEq I] {G : Gauge} {c n : Side}
    {a : I → Site n} {s : Jets.Weights a} {Q : Directions G c → Prop} {P : Prices} {V : Config G c} {M K : ℝ} {k N d : ℕ} {W : Windows I} {A : Jets.Field G c I}

def parcel (p : Run I d) (X : Fin d → Jets.Field G c I) := fun x=> fare p fun i=> X i x
lemma parcel_eq (p : Run I d) (X : Fin d → Jets.Field G c I) (x : Config G c) : parcel p X x=reserved p X x (p 0) (p (Fin.last _)) := (reserved_read p X).symm
lemma filter_left {l : Word G c} (i j : I) (p : Run I d) (f : Config G c→ℝ) : leftDerivs (fun v=> ends i j p (f v)) l V = ends i j p (leftDerivs f l V) := by unfold ends; split_ifs; rfl; simp [Work.G07.left_const]
lemma fare_left {l : Word G c} (i j : I) (B : Fin d → Jets.Field G c I) (hh : ∀ i, Good (B i) l.length V) : leftDerivs (fun v=>build B v i j) l V = ∑ p, ends i j p (leftDerivs (parcel p B) l V) := by
  unfold build; simp_rw [engine_entries]; change leftDerivs (fun v=> ∑ p,ends i j p (parcel p B v)) _ _ = _
  rw [ChangeV.left_sum (fun p v=>ends i j p (parcel p B v)) l V]; swap
  · intro p hp; unfold ends; split_ifs
    · exact (reserved_good hh p (p 0) (p (Fin.last _))).congr_of_eventuallyEq (Eventually.of_forall (fun x => parcel_eq p B (increment V x)))
    exact contDiffAt_const
  simp_rw [filter_left]

variable (W A) in
def sailing (p : Run I (d+2)) (u : ℝ) := parcel p (shifted W A d u)
variable (W A) in
def mailed (p : Run I (d+2)) (v : Config G c) := ∫ u : ℝ in Ioi 0,sailing W A p u v
variable (W A) in
def pushLog (p : Run I (d+1)) (v : Config G c) := (-1/(d+1:ℝ))*parcel p (twist W A d) v
variable (W A) in
def pushQuad (p : Run I (d+2)) := parcel p (extended W A d)

variable (h : Street P s k Q A V M) (hf : Fuel P s k M K) (hx : W.Includes a N)
include h hx hf
local notation "μI" => volume.restrict (Ioi (0:ℝ))
lemma sailing_terms (p : Run I (d+2)) : Terms μI (Ioi 0) Q (sailing W A p) k (fun j u=>Line.bell u * asking s P K N d p j) V := by
  unfold sailing; simp_rw [show ∀ u, parcel p (shifted W A d u)=fun x=> reserved p (shifted W A d u) x (p 0) (p (Fin.last _)) from fun u=>funext (parcel_eq _ _)]
  refine ⟨fun l hl hd=> ((reserved_flow (M':=fun i u=>shifted W A d u i) (shifted_flow h d) (fun i {_} hu=>shifted_good h d i hu.le) p l hl) _ _).aestronglyMeasurable measurableSet_Ioi,
    fun l hl hd u hu=> ?_, fun l hl hd i hi u hu=> (reserved_good (M':=shifted W A d u) (fun j=>shifted_good h d j (le_of_lt hu)) p).has hl i _ _⟩
  exact (((shift_price h hf hx d p (le_of_lt hu)) l hl hd).1.entry (h.room.trans (s.width_le _ _ _ hl)) _ _).trans_eq (by unfold asking; ring)

omit h
variable (h' : ∀ᶠ u in 𝓝 V, Street P s k Q A u M) {l : Word G c} (hl : l.length ≤ k) (hd : ∀ i∈l,Q i)
include h' hl hd
lemma mailed_price (p : Run I (d+2)) : leftDerivs (mailed W A p) l V = ∫ u : ℝ in Ioi 0,leftDerivs (sailing W A p u) l V ∧
      Integrable (fun u=>leftDerivs (sailing W A p u) l V) μI ∧
      ‖leftDerivs (mailed W A p) l V‖ ≤ asking s P K N d p l.length := by
  have hv := ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=(0:ℝ)))
  have H j (_ : j≤k) := Line.bell_int.1.mul_const (asking s P K N d p j)
  have he := h'.mono fun u hu=>sailing_terms hu hf hx p
  exact ⟨inside_total hv H he hl hd,he.self_of_nhds.integrable hv H hl hd,(paid_total hv H he hl hd).trans_eq (by rw [integral_mul_const,Line.bell_int.2,one_mul])⟩

lemma tail_exact (i j : I) (d : ℕ) : leftDerivs (fun v=>W.tail (A v) d i j) l V = ∑ p : Run I (d+2),ends i j p (leftDerivs (mailed W A p) l V) := by
  have hv := ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=(0:ℝ)))
  let F u v := path W A d u v i j
  have ht (u : ℝ) (v : Config G c) : F u v = build (shifted W A d u) v i j := (fare_path ..).trans (engine_entries _ i j).symm
  have he := h'.mono (fun v hh=> hh.path_terms W hx (q:=qd P s k M N) le_rfl i j d)
  change leftDerivs (total μI F) l V= _
  have hp p := mailed_price hf hx h' hl hd
    (p:=(p:Run I (d+2)))
  erw [inside_total hv (fun m _=>Line.bell_int.1.const_mul _) he hl hd]; simp_rw [(hp _).1]
  have ha (u : ℝ) (hu : 0<u) : leftDerivs (F u) l V = ∑ p : Run I (d+2),ends i j p (leftDerivs (sailing W A p u) l V) := by
    simp_rw [show F u=fun v=>build (shifted W A d u) v i j from funext (ht u)]; exact fare_left i j _ (fun i=> (shifted_good h'.self_of_nhds d i hu.le).lower hl)
  rw [integral_congr_ae (hv.mono fun u hu=>ha u hu), integral_finsetSum]; swap
  · intro p _; unfold ends; split_ifs; exact (hp p).2.1; exact integrable_zero _ _ _
  exact Finset.sum_congr rfl fun p _ => by unfold ends; split_ifs; rfl; exact integral_zero _ ℝ

lemma log_values (i j : I) (d : ℕ) : leftDerivs (fun v=>Round.ripple (coeff W A v) d i j) l V = ∑ p : Run I (d+1),ends i j p (leftDerivs (pushLog W A p) l V) := by
  let b := -1/(d+1:ℝ)
  have he v : Round.ripple (coeff W A v) d i j = b * build (twist W A d) v i j := by unfold Round.ripple twist build; rw [engine_pow]; unfold b; ring
  unfold pushLog; simp_rw [he,ChangeV.left_mul]
  rw [fare_left i j _ (fun i=> (twist_good h'.self_of_nhds d i).lower hl),Finset.mul_sum]; simp [ends,b,mul_ite]
lemma quad_values (i j : I) (d : ℕ) : leftDerivs (fun v=> (((-(coeff W A v))^(d+1))* A v) i j) l V = ∑ p : Run I (d+2),ends i j p (leftDerivs (pushQuad W A p) l V) := by
  simp_rw [(fare_extended d i j).trans (engine_entries _ i j).symm]; exact fare_left i j _ (fun i=> (extended_good h'.self_of_nhds d i).lower hl)
lemma push_prices (p : Run I (d+1)) : ‖leftDerivs (pushLog W A p) l V‖ ≤ asking s P K N d p l.length := by
  unfold pushLog; rw [ChangeV.left_mul,norm_mul]
  apply le_trans (mul_le_of_le_one_left (norm_nonneg _) (by simp [norm_div, Real.norm_of_nonneg (by positivity : 0≤(d+1:ℝ)), inv_le_one_of_one_le₀] : ‖-(1:ℝ)/(d+1)‖≤1))
  have h := h'.self_of_nhds
  exact (by simp_rw [show parcel p (twist W A d)=fun v=>reserved p (twist W A d) v (p 0) (p (Fin.last _)) from funext (parcel_eq _ _)]
            exact ((twist_price h hf hx (h'.mono fun _ h=>h.base.symm) d p) l hl hd).1.entry (h.room.trans (s.width_le _ _ _ hl)) _ _)
lemma quad_prices (p : Run I (d+2)) : ‖leftDerivs (pushQuad W A p) l V‖ ≤ asking s P K N d p l.length := by
  have h := h'.self_of_nhds
  simp_rw [pushQuad, show parcel p (extended W A d)=fun v=>reserved p (extended W A d) v (p 0) (p (Fin.last _)) from funext (parcel_eq _ _)]
  exact ((extended_price h hf hx (h'.mono fun _ h=>h.base.symm) d p) l hl hd).1.entry (h.room.trans (s.width_le _ _ _ hl)) _ _
end YM.Further.CurvedGaussianJets.Tracks
