import YM.RG08.Cell.Release

/-!
# The conditional predictor in the same Gaussian slice convention
-/
noncomputable section
namespace YM.RG08.Cell
open Stationary Function Matrix Lattice Exterior Precision RG Tree Wilson Laurent Bloch Finset RG08.Rows RG08.Flat Pert.Bulk RG08.Packets RG08.Line
open scoped Matrix BigOperators Topology Classical
set_option autoImplicit false
variable (P : Patch)(K:KernelChoices)(G:Gauge)

-- path_read private / hike_face returns projection to fixed root scalar. mean output axial vector uses A function constant x,v axis. price similarly with path extension. instead express via existing bonds_spot on repack patron directly, fund via `readsPrice` indexed list per i or Fin point,k via `rout`.
lemma mean_bill : Fund (α:=Loc G 1) (β:=Co P.L (Loc G 1)) fun n=> let S:=habitat P K n; repackM (Equiv.refl _) (unitSplit G S 1) (bondsM G S):= by
  let I := P.Points × Fin (P.L.val)
  let z (t:I) (i:Loc G 1):Cover:= t.1.val+t.2.val • step (axisEquiv.symm i.1)
  let y t i : Co P.L (Loc G 1):=(wrap P.L (z t i),i)
  let C (t:I): Matrix (Loc G 1) (Co P.L (Loc G 1)) ℝ:= Matrix.of fun i a=> if a=y t i then P.weight t.1 else 0
  refine Fund.rout _ C (fun t i _=> rent P.L (z t i)) _ fun n h i=> ?_
  let S:=habitat P K n
  erw [repack_test,bonds_spot]
  simp only [C,Matrix.of_apply,ite_mul,zero_mul, Finset.sum_ite_eq',Finset.mem_univ, if_true]
  dsimp [I]; rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j hj=>?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu=>?_
  -- reduce to pack_street
  change P.weight j * h ((splitCo S.ratio _) ((wrap _ j.val+S.ratio.embed i.1+u.val • step (axisEquiv.symm i.2.1)),i.2))=_
  rw [show (wrap _ j.val+S.ratio.embed i.1+u.val • step (axisEquiv.symm i.2.1)) = wrap _ (z ((j,u):I) i.2)+S.ratio.embed i.1 from by unfold z; rw [map_add,map_nsmul,wrap_step]; abel]
  erw [pack_street]

lemma edge0 : Fund (α:=Loc G 1) (β:=Loc G 0) fun n=>patron G (d 0 n):= by
  convert dyed G (Fund.ticket (cobound 0) Exterior.support (certified 0)) using 1
  funext n; ext x y; exact patron_cell G (d 0 n) (x.1,x.2.1) (y.1,y.2.1) x.2.2 y.2.2

lemma probe_bill : Fund (α:=Loc G 1) (β:=Co P.L (Loc G 1)) fun n=> let S:=habitat P K n; repackM (Equiv.refl _) (unitSplit G S 1) (patron G (probe S)):= by
  have ht:=edge0 G
  have he:=fundCF P K G (fixPrice P K)
  convert (mean_bill P K G).plus (ht.times he) using 1
  funext n
  let S:=habitat P K n
  dsimp only
  unfold Precision.probe
  rw [ink_add_general, patron_mul]
  erw [show repackM (Equiv.refl _) (unitSplit G S 1) (patron G (mean S)+patron G (d 0 n) * _) = repackM (Equiv.refl _) (unitSplit G S 1) (patron G (mean S)) + repackM (Equiv.refl _) (unitSplit G S 1) (patron G (d 0 n) * patron G (fixRoot S)) from rfl,
    repack_multiply (Equiv.refl _) (Equiv.refl (Lines G n 0))]
  rfl

def probe_receipt := (((probe_bill P K G) 1 zero_le_one).choose_spec.choose) -- common kernel pick with fare := .choose

def toll_probe := ((probe_bill P K G) 1 zero_le_one).choose

lemma probes_on : Tagged 1 (toll_probe P K G) (probe_receipt P K G) (fun n=> let S:=habitat P K n; repackM (Equiv.refl _) (unitSplit G S 1) (patron G (probe S))):= ((probe_bill P K G 1 zero_le_one).choose_spec).choose_spec

/-- Candidate analytic A_tr. -/
def predictor (b : Bed) := K.penalty • Pert.Bulk.bind (warm P K G b) (swap (probe_receipt P K G))

-- finite agreement
variable {c f : Side}

def predictorFinite (P : Patch)(K:KernelChoices)(G:Gauge)(b:Bed)(n:Side): Matrix (Co n (Co P.L (Loc G 1))) (Co n (Loc G 1)) ℝ:= let S:=habitat P K n; let v:=repackM (Equiv.refl _) (unitSplit G S 1) (patron G (probe S)); K.penalty • (cellLine P K G b n * (show Matrix (Co n (Co P.L (Loc G 1))) (Co n (Loc G 1)) ℝ from v.transpose))

def RootField (S : StepData c f) (b : Bed) : Matrix (Lines G f 1) (Lines G c 1) ℝ := K.penalty • (NativeLine S G b * (patron G (probe S)).transpose)

lemma root_read (b : Bed)(n:Side) : let S:=habitat P K n; repackM (unitSplit G S 1) (Equiv.refl _) (RootField K G S b)=predictorFinite P K G b n:= by
  intro S
  unfold RootField predictorFinite
  erw [repack_scale,repack_multiply _ (unitSplit G S 1),repack_rotate,native_paid]; rfl -- native_paid direction? rw rhs rewrites to LHS.

def key (P:Patch)(K:KernelChoices) := K.penalty * (Fintype.card (Co P.L (Loc G 1)):ℝ)*toll_probe P K G

lemma predictor_price {η B:ℝ}(b:Bed) (h:Warm G K P b η B)(he:0≤η)(hs:η≤1):
    Tagged η (B*key G P K) (predictor P K G b) (predictorFinite P K G b):= by
  have hp:= (h.bill.mul (((probes_on P K G).mono hs le_rfl).rear he) he).smul K.penalty
  convert hp using 1
  rw [abs_of_nonneg K.penalty_pos.le]; unfold key; ring
  all_goals rfl

-- exact conditional stationary equality when tested -- no claim yet of pre-L bounds on this
-- tree-slice column itself (they belong on the gauge-equiv representative A0).
lemma tree_station {n m:Side}{S : StepData n m}{b b':Bed}{A : Matrix (Body 1 m) (Body 1 n) ℝ}
    (hd : K=S.kernel) (F : Forest S.ratio) (Γ : Matrix (Lines G m 1) (Lines G m 1) ℝ)
    (he : ∀ x,onTree F x → Γ *ᵥ (linePrecision G S b *ᵥ x)=x)
    (h : Inputs S A (b.metric.acts m) (b'.metric.acts n)) :
    K.penalty • (Γ*(patron G (probe S)).transpose) = patron G (extracted S F A) := by
  subst K
  let V:=extracted S F A
  have ht := stationed F A _ _ h
  have hh : linePrecision G S b * patron G V=S.kernel.penalty • (patron G (probe S)).transpose := by
    unfold linePrecision
    rw [← patron_mul,Matrix.add_mul,Matrix.smul_mul,Matrix.mul_assoc (probe S).transpose, ht.1,ht.2,Matrix.mul_sub,Matrix.mul_smul,Matrix.mul_one,smul_sub,smul_smul,mul_inv_cancel₀ S.kernel.penalty_pos.ne',one_smul,add_sub_cancel,ink_factor_general,patron_star]
  refine perVec fun v=> ?_
  let w:= patron G V *ᵥ v -- stays
  have hw:onTree F w:=fun k j hj=>by
    unfold w
    dsimp only
    rw [painted G V _ k ((j.1,coord j.2):Body 1 m), Precision.stays F A _ j hj]
  let hhO := he _ hw
  rw [← Matrix.mul_smul, ← hh, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]; exact hhO
end YM.RG08.Cell
